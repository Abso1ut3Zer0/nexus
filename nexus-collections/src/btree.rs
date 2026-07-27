//! B-tree sorted map with external slab allocation.
//!
//! # Design
//!
//! A cache-friendly sorted map where each node stores up to B-1 key-value
//! pairs and up to B child pointers. High fanout means fewer pointer chases
//! per lookup — at B=8 a 10k-entry tree is only 3-4 levels deep.
//!
//! # Allocation Model
//!
//! The tree does NOT store the slab. The slab is passed to methods that
//! allocate or free nodes. Read-only methods do not need the slab.
//!
//! # Example
//!
//! ```ignore
//! use nexus_slab::bounded::Slab;
//! use nexus_collections::btree::{BTree, BTreeNode};
//!
//! let slab = unsafe { Slab::<BTreeNode<u64, String, 8>>::with_capacity(1000) };
//! let mut map = BTree::<u64, String, 8>::new();
//! map.try_insert(&slab, 100, "hello".into()).unwrap();
//! assert_eq!(map.get(&100), Some(&"hello".into()));
//! ```

use std::cmp::Ordering;
use std::fmt;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ptr;

use nexus_slab::bounded;
use nexus_slab::shared::{Full, Slot, SlotCell};

use crate::SlabOps;
use crate::compare::{Compare, Natural};

// =============================================================================
// Constants
// =============================================================================

const MAX_DEPTH: usize = 32;

// =============================================================================
// NodePtr
// =============================================================================

type NodePtr<K, V, const B: usize> = *mut SlotCell<BTreeNode<K, V, B>>;

// =============================================================================
// BTreeNode<K, V, B>
// =============================================================================

/// A node in a B-tree sorted map.
#[repr(C)]
pub struct BTreeNode<K, V, const B: usize> {
    len: u16,
    leaf: bool,
    keys: [MaybeUninit<K>; B],
    values: [MaybeUninit<V>; B],
    children: [NodePtr<K, V, B>; B],
}

impl<K, V, const B: usize> BTreeNode<K, V, B> {
    fn new_leaf() -> Self {
        BTreeNode {
            len: 0,
            leaf: true,
            keys: [const { MaybeUninit::uninit() }; B],
            values: [const { MaybeUninit::uninit() }; B],
            children: [ptr::null_mut(); B],
        }
    }

    fn new_internal() -> Self {
        BTreeNode {
            len: 0,
            leaf: false,
            keys: [const { MaybeUninit::uninit() }; B],
            values: [const { MaybeUninit::uninit() }; B],
            children: [ptr::null_mut(); B],
        }
    }
}

// =============================================================================
// node_deref
// =============================================================================

/// # Safety
///
/// `ptr` must be non-null and point to an occupied `SlotCell`.
unsafe fn node_deref<K, V, const B: usize>(ptr: NodePtr<K, V, B>) -> *const BTreeNode<K, V, B> {
    // SAFETY: SlotCell::value_ptr() returns the pointer to the stored value.
    unsafe { (*ptr).value_ptr() }
}

/// # Safety
///
/// `ptr` must be non-null and point to an occupied `SlotCell`. The caller
/// must ensure no other references to this node exist.
unsafe fn node_deref_mut<K, V, const B: usize>(ptr: NodePtr<K, V, B>) -> *mut BTreeNode<K, V, B> {
    // Use value_ptr_mut to avoid creating &SlotCell which would give
    // read-only provenance under stacked borrows.
    // SAFETY: ptr is non-null and points to an occupied SlotCell per caller contract.
    unsafe { nexus_slab::shared::SlotCell::value_ptr_mut(ptr) }
}

// =============================================================================
// Node accessor helpers
// =============================================================================

/// # Safety: `ptr` must be a valid non-null B-tree node.
unsafe fn node_len<K, V, const B: usize>(ptr: NodePtr<K, V, B>) -> usize {
    // SAFETY: ptr is non-null and points to an occupied SlotCell per caller contract.
    unsafe { (*node_deref(ptr)).len as usize }
}

/// # Safety: `ptr` must be a valid non-null B-tree node.
unsafe fn node_is_leaf<K, V, const B: usize>(ptr: NodePtr<K, V, B>) -> bool {
    // SAFETY: ptr is non-null and points to an occupied SlotCell per caller contract.
    unsafe { (*node_deref(ptr)).leaf }
}

/// # Safety: `ptr` must be a valid node, `i < node.len`.
unsafe fn key_at<'a, K, V, const B: usize>(ptr: NodePtr<K, V, B>, i: usize) -> &'a K {
    // SAFETY: keys[i] is initialized for i < node.len.
    unsafe { (*node_deref(ptr)).keys[i].assume_init_ref() }
}

/// # Safety: `ptr` must be a valid node, `i < node.len`.
unsafe fn value_at<'a, K, V, const B: usize>(ptr: NodePtr<K, V, B>, i: usize) -> &'a V {
    // SAFETY: values[i] is initialized for i < node.len.
    unsafe { (*node_deref(ptr)).values[i].assume_init_ref() }
}

/// # Safety: `ptr` must be a valid node, `i < node.len`. Caller ensures exclusivity.
unsafe fn value_at_mut<'a, K, V, const B: usize>(ptr: NodePtr<K, V, B>, i: usize) -> &'a mut V {
    // SAFETY: values[i] is initialized for i < node.len.
    unsafe { (*node_deref_mut(ptr)).values[i].assume_init_mut() }
}

/// # Safety: `ptr` must be a valid non-leaf node, `i <= node.len`.
unsafe fn child_at<K, V, const B: usize>(ptr: NodePtr<K, V, B>, i: usize) -> NodePtr<K, V, B> {
    // SAFETY: ptr is non-null and points to an occupied SlotCell; i <= node.len per caller.
    unsafe { (*node_deref(ptr)).children[i] }
}

/// # Safety: `ptr` must be a valid non-null B-tree node.
unsafe fn search_in_node<K, V, const B: usize, C: Compare<K>>(
    ptr: NodePtr<K, V, B>,
    key: &K,
) -> (usize, bool) {
    // SAFETY: ptr is a valid node per caller contract.
    let node = unsafe { &*node_deref(ptr) };
    let len = node.len as usize;
    let mut i = 0;
    while i < len {
        // SAFETY: keys[i] is initialized for i < len.
        let k = unsafe { node.keys[i].assume_init_ref() };
        match C::cmp(key, k) {
            Ordering::Equal => return (i, true),
            Ordering::Less => return (i, false),
            Ordering::Greater => {}
        }
        i += 1;
    }
    (len, false)
}

// =============================================================================
// Node mutation helpers
// =============================================================================

/// Takes (moves out) the key-value pair at index `i`.
///
/// # Safety: `ptr` must be a valid node, `i < node.len`.
/// The slot at `i` is left uninitialized after this call.
unsafe fn take_kv<K, V, const B: usize>(ptr: NodePtr<K, V, B>, i: usize) -> (K, V) {
    // SAFETY: keys[i] and values[i] are initialized for i < node.len.
    let node = unsafe { &*node_deref(ptr) };
    // SAFETY: keys[i] is initialized for i < node.len per caller contract.
    let k = unsafe { node.keys[i].assume_init_read() };
    // SAFETY: same invariant as above; values[i] is initialized for i < node.len.
    let v = unsafe { node.values[i].assume_init_read() };
    (k, v)
}

/// Shifts keys/values/children right by one starting at index `i`, making
/// room for an insertion. Does not update `len`.
///
/// # Safety
///
/// - `ptr` must be a valid node obtained from `Slot::into_raw()`.
/// - `node.len < B-1` (room exists), so after the shift the last
///   element lands at index `len` which is within the array of size B.
/// - `i <= node.len`. Elements at [i..len) are initialized and moved to
///   [i+1..len+1). The slot at `i` is left in a moved-from state.
unsafe fn shift_right<K, V, const B: usize>(ptr: NodePtr<K, V, B>, i: usize) {
    // SAFETY: ptr is a valid node per caller contract. ptr::copy handles
    // overlapping regions correctly (memmove semantics).
    let node = unsafe { &mut *node_deref_mut(ptr) };
    let len = node.len as usize;
    if i < len {
        // SAFETY: keys/values at [i..len) are initialized; len < B-1 ensures [i+1..len+1)
        // is within the array. ptr::copy handles overlapping regions (memmove semantics).
        unsafe {
            let kp = node.keys.as_mut_ptr();
            ptr::copy(kp.add(i).cast_const(), kp.add(i + 1), len - i);
            let vp = node.values.as_mut_ptr();
            ptr::copy(vp.add(i).cast_const(), vp.add(i + 1), len - i);
        }
    }
    if !node.leaf && i < len {
        // SAFETY: internal node has valid children at [i+1..=len]; len < B-1 so
        // shifting to [i+2..=len+1] fits in the children array of size B.
        unsafe {
            let cp = node.children.as_mut_ptr();
            ptr::copy(cp.add(i + 1).cast_const(), cp.add(i + 2), len - i);
        }
    }
}

/// Shifts keys/values/children left by one at index `i`, removing the
/// element at `i`. Decrements `len`.
///
/// # Safety
///
/// - `ptr` must be a valid node obtained from `Slot::into_raw()`.
/// - `i < node.len`. The caller must have already moved out (or dropped)
///   keys[i] and values[i] before calling, since this function overwrites
///   slot `i` with slot `i+1` via ptr::copy (no drop is run).
/// - For internal nodes with children, children[i+1..=len] are shifted
///   to [i..len-1], removing children[i+1]. This is correct after a merge
///   where children[merge_idx+1] was freed and should be removed.
unsafe fn shift_left<K, V, const B: usize>(ptr: NodePtr<K, V, B>, i: usize) {
    // SAFETY: ptr is a valid node per caller contract.
    let node = unsafe { &mut *node_deref_mut(ptr) };
    let len = node.len as usize;
    if i + 1 < len {
        // SAFETY: [i+1..len) are initialized keys/values (caller moved out slot i);
        // ptr::copy handles overlap when shifting left by 1 over len-i-1 elements.
        unsafe {
            let kp = node.keys.as_mut_ptr();
            ptr::copy(kp.add(i + 1).cast_const(), kp.add(i), len - i - 1);
            let vp = node.values.as_mut_ptr();
            ptr::copy(vp.add(i + 1).cast_const(), vp.add(i), len - i - 1);
        }
    }
    if !node.leaf && i + 2 <= len {
        // SAFETY: internal node with `len` keys has valid children at [i+2..=len];
        // shifting to [i+1..len-1] removes the right child of the eliminated separator.
        unsafe {
            let cp = node.children.as_mut_ptr();
            ptr::copy(cp.add(i + 2).cast_const(), cp.add(i + 1), len - i - 1);
        }
    }
    node.len -= 1;
}

/// Drops all initialized keys/values in the node, then frees the slab slot.
///
/// # Safety: `ptr` must be a valid non-null node. Children must already be
/// freed or otherwise handled by the caller.
unsafe fn free_node<K, V, const B: usize>(
    ptr: NodePtr<K, V, B>,
    slab: &impl SlabOps<BTreeNode<K, V, B>>,
) {
    // SAFETY: ptr is a valid node per caller contract.
    let node = unsafe { &mut *node_deref_mut(ptr) };
    for i in 0..node.len as usize {
        // SAFETY: keys[i] and values[i] are initialized for i < len.
        unsafe {
            node.keys[i].assume_init_drop();
            node.values[i].assume_init_drop();
        }
    }
    // SAFETY: ptr was obtained from Slot::into_raw() during insert/split.
    let slot = unsafe { Slot::from_raw(ptr) };
    slab.free_slot(slot);
}

/// Splits the child at `child_idx` of `parent`. The right half goes into
/// `right_ptr` (a freshly allocated empty node). The median key-value is
/// promoted into the parent.
///
/// # Safety
///
/// - `parent` must be a valid non-full internal node (len < B-1), obtained
///   from `Slot::into_raw()` during a prior insert or root split.
/// - `child_idx <= parent.len`, pointing to a valid child that is full
///   (len == B-1).
/// - `right_ptr` must be a freshly allocated empty node of the correct
///   leaf/internal type, also from `Slot::into_raw()`.
unsafe fn split_child_core<K, V, const B: usize>(
    parent: NodePtr<K, V, B>,
    child_idx: usize,
    right_ptr: NodePtr<K, V, B>,
) {
    // SAFETY: parent is a valid internal node per caller contract.
    // child_at reads children[child_idx] which is valid because
    // child_idx <= parent.len for an internal node.
    let child = unsafe { child_at(parent, child_idx) };
    // SAFETY: child was stored in parent.children during a prior insert or
    // root init, so it points to an occupied SlotCell. right_ptr was just
    // allocated by the caller. No other references exist to either node.
    let child_node = unsafe { &mut *node_deref_mut(child) };
    // SAFETY: right_ptr was just allocated by the caller and points to an occupied SlotCell.
    let right_node = unsafe { &mut *node_deref_mut(right_ptr) };
    let child_is_leaf = child_node.leaf;

    let mid = (B - 1) / 2;
    let right_len = B - 1 - mid - 1;

    // SAFETY: child was full (len == B-1), so keys[0..B-1] and values[0..B-1]
    // are all initialized. We copy from indices [mid+1 .. B-1] which is
    // right_len elements. Destination is a freshly allocated node with
    // uninitialized arrays — no overlap. right_len + mid + 1 == B-1 so
    // source indices are within [0, B-1).
    unsafe {
        ptr::copy_nonoverlapping(
            child_node.keys.as_ptr().add(mid + 1),
            right_node.keys.as_mut_ptr(),
            right_len,
        );
        ptr::copy_nonoverlapping(
            child_node.values.as_ptr().add(mid + 1),
            right_node.values.as_mut_ptr(),
            right_len,
        );
    }

    if !child_is_leaf {
        // SAFETY: an internal node with len == B-1 has B valid children at
        // indices [0..B-1]. We copy children[mid+1 .. B-1] which is
        // right_len + 1 pointers. All are valid non-null child pointers
        // set during prior splits/inserts.
        unsafe {
            ptr::copy_nonoverlapping(
                child_node.children.as_ptr().add(mid + 1),
                right_node.children.as_mut_ptr(),
                right_len + 1,
            );
        }
    }
    right_node.len = right_len as u16;
    right_node.leaf = child_is_leaf;

    // SAFETY: keys[mid] and values[mid] are initialized because child was
    // full (len == B-1) and mid < B-1. assume_init_read moves the value
    // out; the slot becomes logically uninitialized (child.len set to mid
    // below, so it won't be accessed again).
    let median_key = unsafe { child_node.keys[mid].assume_init_read() };
    // SAFETY: same invariant as above; values[mid] is initialized because child was full (len == B-1).
    let median_value = unsafe { child_node.values[mid].assume_init_read() };
    child_node.len = mid as u16;

    // SAFETY: parent.len < B-1 (caller contract: non-full parent), so
    // shift_right has room to move elements right by one at child_idx.
    unsafe { shift_right(parent, child_idx) };

    // SAFETY: parent is valid and we just made room at child_idx via
    // shift_right. child_idx < B-1 after the shift.
    let parent_node = unsafe { &mut *node_deref_mut(parent) };
    parent_node.keys[child_idx] = MaybeUninit::new(median_key);
    parent_node.values[child_idx] = MaybeUninit::new(median_value);
    parent_node.children[child_idx + 1] = right_ptr;
    parent_node.len += 1;
}

// =============================================================================
// BTree<K, V, B, C>
// =============================================================================

/// A cache-friendly sorted map with external slab allocation.
///
/// # Panic Safety
///
/// If a comparator panics during a tree mutation (insert/remove), the tree
/// may be left in an inconsistent state with partially-updated node splits
/// or merges. Subsequent operations on such a tree are undefined behavior.
/// Callers are responsible for ensuring their `Compare` implementation does
/// not panic.
pub struct BTree<K, V, const B: usize = 8, C = Natural> {
    root: NodePtr<K, V, B>,
    len: usize,
    depth: usize,
    _marker: PhantomData<C>,
}

// =============================================================================
// impl — base block (requires Compare)
// =============================================================================

impl<K, V, const B: usize, C: Compare<K>> BTree<K, V, B, C> {
    /// Returns `true` if the tree contains the given key.
    pub fn contains_key(&self, key: &K) -> bool {
        self.find(key).is_some()
    }

    /// Returns a reference to the value for the given key.
    pub fn get(&self, key: &K) -> Option<&V> {
        let (ptr, idx) = self.find(key)?;
        // SAFETY: find() returned a valid node and index where the key was found.
        Some(unsafe { value_at(ptr, idx) })
    }

    /// Returns a mutable reference to the value for the given key.
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let (ptr, idx) = self.find(key)?;
        // SAFETY: find() returned a valid node and index; &mut self ensures exclusivity.
        Some(unsafe { value_at_mut(ptr, idx) })
    }

    /// Returns references to the key and value for the given key.
    pub fn get_key_value(&self, key: &K) -> Option<(&K, &V)> {
        let (ptr, idx) = self.find(key)?;
        // SAFETY: find() returned a valid node and index.
        Some(unsafe { (key_at(ptr, idx), value_at(ptr, idx)) })
    }

    // =========================================================================
    // Remove / pop / clear
    // =========================================================================

    /// Removes the node with the given key and returns the value.
    pub fn remove(&mut self, slab: &impl SlabOps<BTreeNode<K, V, B>>, key: &K) -> Option<V> {
        let (_, v) = self.remove_entry(slab, key)?;
        Some(v)
    }

    /// Removes the node with the given key and returns `(key, value)`.
    pub fn remove_entry(
        &mut self,
        slab: &impl SlabOps<BTreeNode<K, V, B>>,
        key: &K,
    ) -> Option<(K, V)> {
        if self.root.is_null() {
            return None;
        }

        let mut path: [(NodePtr<K, V, B>, usize); MAX_DEPTH] = [(ptr::null_mut(), 0); MAX_DEPTH];
        let mut path_len = 0usize;
        let mut current = self.root;

        loop {
            // SAFETY: current is non-null — initialized from self.root (checked above)
            // or from child_at on a valid internal node. search_in_node requires a
            // valid node pointer.
            let (idx, found) = unsafe { search_in_node::<K, V, B, C>(current, key) };
            if found {
                // SAFETY: current is a valid node, idx < node.len (found == true).
                let result = unsafe { self.remove_found(slab, current, idx, &path, path_len) };
                self.len -= 1;

                return Some(result);
            }
            // SAFETY: current is a valid node.
            if unsafe { node_is_leaf(current) } {
                return None;
            }
            debug_assert!(path_len < MAX_DEPTH);
            path[path_len] = (current, idx);
            path_len += 1;
            // SAFETY: current is a valid internal node, idx <= node.len.
            let next = unsafe { child_at(current, idx) };
            current = next;
        }
    }

    /// Removes and returns the first (smallest) key-value pair.
    pub fn pop_first(&mut self, slab: &impl SlabOps<BTreeNode<K, V, B>>) -> Option<(K, V)> {
        if self.root.is_null() {
            return None;
        }

        let mut path: [(NodePtr<K, V, B>, usize); MAX_DEPTH] = [(ptr::null_mut(), 0); MAX_DEPTH];
        let mut path_len = 0usize;
        let mut current = self.root;

        // SAFETY: all node_is_leaf/child_at calls below operate on `current`,
        // which starts as self.root (non-null, checked above) and each iteration
        // replaces it with a valid child pointer from a valid internal node.
        while !unsafe { node_is_leaf(current) } {
            debug_assert!(path_len < MAX_DEPTH);
            path[path_len] = (current, 0);
            path_len += 1;
            // SAFETY: current is a valid internal node; children[0] is the leftmost valid child.
            let next = unsafe { child_at(current, 0) };
            current = next;
        }

        // SAFETY: current is a valid leaf node with at least 1 key (tree is non-empty).
        // take_kv reads initialized key/value at index 0. shift_left closes the gap.
        let result = unsafe { take_kv(current, 0) };
        // SAFETY: current is a valid leaf; shift_left closes the gap and decrements len.
        unsafe { shift_left(current, 0) };
        self.fixup_after_remove(slab, current, &path, path_len);
        self.len -= 1;

        Some(result)
    }

    /// Removes and returns the last (largest) key-value pair.
    pub fn pop_last(&mut self, slab: &impl SlabOps<BTreeNode<K, V, B>>) -> Option<(K, V)> {
        if self.root.is_null() {
            return None;
        }

        let mut path: [(NodePtr<K, V, B>, usize); MAX_DEPTH] = [(ptr::null_mut(), 0); MAX_DEPTH];
        let mut path_len = 0usize;
        let mut current = self.root;

        // SAFETY: all node_is_leaf/node_len/child_at calls below operate on `current`,
        // which starts as self.root (non-null, checked above) and each iteration
        // replaces it with a valid child pointer from a valid internal node.
        while !unsafe { node_is_leaf(current) } {
            // SAFETY: current is a valid internal node on this loop iteration.
            let len = unsafe { node_len(current) };
            debug_assert!(path_len < MAX_DEPTH);
            path[path_len] = (current, len);
            path_len += 1;
            // SAFETY: current is a valid internal node; children[len] is the rightmost valid child.
            let next = unsafe { child_at(current, len) };
            current = next;
        }

        // SAFETY: current is a valid leaf with at least 1 key (tree is non-empty).
        // take_kv reads initialized key/value at the last index. Decrementing len
        // logically removes the last slot (already moved out by take_kv).
        let last = unsafe { node_len(current) } - 1;
        // SAFETY: last == node.len - 1 < node.len, so keys[last] and values[last] are initialized.
        let result = unsafe { take_kv(current, last) };
        // SAFETY: current is a valid node; take_kv moved out the last slot, decrementing len is sound.
        unsafe { (*node_deref_mut(current)).len -= 1 };
        self.fixup_after_remove(slab, current, &path, path_len);
        self.len -= 1;

        Some(result)
    }

    // =========================================================================
    // Insert
    // =========================================================================

    /// Inserts a key-value pair, or returns the pair if the slab is full.
    ///
    /// Use with a [`bounded::Slab`]. For an infallible insert with an
    /// unbounded slab, see [`insert`](Self::insert).
    pub fn try_insert(
        &mut self,
        slab: &bounded::Slab<BTreeNode<K, V, B>>,
        key: K,
        value: V,
    ) -> Result<Option<V>, Full<(K, V)>> {
        let (_, old) = self.try_insert_inner(slab, key, value)?;
        Ok(old)
    }

    /// Inserts a key-value pair. Cannot fail — the unbounded slab grows as needed.
    pub fn insert(
        &mut self,
        slab: &nexus_slab::unbounded::Slab<BTreeNode<K, V, B>>,
        key: K,
        value: V,
    ) -> Option<V> {
        let (_, old) = self.insert_inner(slab, key, value);
        old
    }

    // =========================================================================
    // Entry API
    // =========================================================================

    /// Gets the entry for the given key.
    ///
    /// Works with both [`bounded::Slab`] and [`unbounded::Slab`](nexus_slab::unbounded::Slab).
    /// The available insert methods on [`VacantEntry`] depend on the slab type:
    /// bounded gives [`try_insert`](VacantEntry::try_insert) and [`insert`](VacantEntry::insert),
    /// unbounded gives only [`insert`](VacantEntry::insert).
    pub fn entry<'a, S: SlabOps<BTreeNode<K, V, B>>>(
        &'a mut self,
        slab: &'a S,
        key: K,
    ) -> Entry<'a, K, V, B, C, S> {
        let mut current = self.root;
        while !current.is_null() {
            // SAFETY: current is non-null and a valid tree node (root or child).
            let (idx, found) = unsafe { search_in_node::<K, V, B, C>(current, &key) };
            if found {
                drop(key);
                return Entry::Occupied(OccupiedEntry {
                    tree: self,
                    slab,
                    node: current,
                    idx,
                });
            }
            // SAFETY: current is a valid node.
            if unsafe { node_is_leaf(current) } {
                break;
            }
            // SAFETY: current is a valid internal node, idx <= node.len.
            let next = unsafe { child_at(current, idx) };
            current = next;
        }

        Entry::Vacant(VacantEntry {
            tree: self,
            slab,
            key,
        })
    }

    // =========================================================================
    // Iteration
    // =========================================================================

    /// Returns an iterator over `(&K, &V)` pairs in sorted order.
    pub fn iter(&self) -> Iter<'_, K, V, B> {
        let mut it = Iter {
            stack: [(ptr::null_mut(), 0u16); MAX_DEPTH],
            stack_len: 0,
            remaining: self.len,
            _marker: PhantomData,
        };
        if !self.root.is_null() {
            push_leftmost_path(self.root, &mut it.stack, &mut it.stack_len);
        }
        it
    }

    /// Returns an iterator over keys in sorted order.
    pub fn keys(&self) -> Keys<'_, K, V, B> {
        Keys { inner: self.iter() }
    }

    /// Returns an iterator over values in key-sorted order.
    pub fn values(&self) -> Values<'_, K, V, B> {
        Values { inner: self.iter() }
    }

    /// Returns a mutable iterator over `(&K, &mut V)` pairs in sorted order.
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V, B> {
        let mut it = IterMut {
            stack: [(ptr::null_mut(), 0u16); MAX_DEPTH],
            stack_len: 0,
            remaining: self.len,
            _marker: PhantomData,
        };
        if !self.root.is_null() {
            push_leftmost_path(self.root, &mut it.stack, &mut it.stack_len);
        }
        it
    }

    /// Returns a mutable iterator over values in key-sorted order.
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V, B> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }

    /// Returns an iterator over `(&K, &V)` pairs within the given range.
    pub fn range<R: std::ops::RangeBounds<K>>(&self, range: R) -> Range<'_, K, V, B> {
        use std::ops::Bound;
        let mut it = Range {
            stack: [(ptr::null_mut(), 0u16); MAX_DEPTH],
            stack_len: 0,
            end_node: ptr::null_mut(),
            end_idx: 0,
            _marker: PhantomData,
        };
        if self.root.is_null() {
            return it;
        }

        match range.start_bound() {
            Bound::Unbounded => {
                push_leftmost_path(self.root, &mut it.stack, &mut it.stack_len);
            }
            Bound::Included(k) => {
                init_lower_bound_stack::<K, V, B, C>(
                    self.root,
                    k,
                    &mut it.stack,
                    &mut it.stack_len,
                );
            }
            Bound::Excluded(k) => {
                init_upper_bound_stack::<K, V, B, C>(
                    self.root,
                    k,
                    &mut it.stack,
                    &mut it.stack_len,
                );
            }
        }
        match range.end_bound() {
            Bound::Unbounded => {}
            Bound::Excluded(k) => {
                let (n, i) = self.lower_bound_pos(k);
                it.end_node = n;
                it.end_idx = i;
            }
            Bound::Included(k) => {
                let (n, i) = self.upper_bound_pos(k);
                it.end_node = n;
                it.end_idx = i;
            }
        }
        if it.stack_len > 0 && !it.end_node.is_null() {
            let (sn, si) = it.stack[it.stack_len - 1];
            if sn == it.end_node && si == it.end_idx {
                it.stack_len = 0;
            }
        }
        it
    }

    /// Returns a mutable iterator over `(&K, &mut V)` pairs within the given range.
    pub fn range_mut<R: std::ops::RangeBounds<K>>(&mut self, range: R) -> RangeMut<'_, K, V, B> {
        use std::ops::Bound;
        let mut it = RangeMut {
            stack: [(ptr::null_mut(), 0u16); MAX_DEPTH],
            stack_len: 0,
            end_node: ptr::null_mut(),
            end_idx: 0,
            _marker: PhantomData,
        };
        if self.root.is_null() {
            return it;
        }

        match range.start_bound() {
            Bound::Unbounded => {
                push_leftmost_path(self.root, &mut it.stack, &mut it.stack_len);
            }
            Bound::Included(k) => {
                init_lower_bound_stack::<K, V, B, C>(
                    self.root,
                    k,
                    &mut it.stack,
                    &mut it.stack_len,
                );
            }
            Bound::Excluded(k) => {
                init_upper_bound_stack::<K, V, B, C>(
                    self.root,
                    k,
                    &mut it.stack,
                    &mut it.stack_len,
                );
            }
        }
        match range.end_bound() {
            Bound::Unbounded => {}
            Bound::Excluded(k) => {
                let (n, i) = self.lower_bound_pos(k);
                it.end_node = n;
                it.end_idx = i;
            }
            Bound::Included(k) => {
                let (n, i) = self.upper_bound_pos(k);
                it.end_node = n;
                it.end_idx = i;
            }
        }
        if it.stack_len > 0 && !it.end_node.is_null() {
            let (sn, si) = it.stack[it.stack_len - 1];
            if sn == it.end_node && si == it.end_idx {
                it.stack_len = 0;
            }
        }
        it
    }

    // =========================================================================
    // Cursor
    // =========================================================================

    /// Returns a cursor positioned before the first element.
    pub fn cursor_front<'a, S: SlabOps<BTreeNode<K, V, B>>>(
        &'a mut self,
        slab: &'a S,
    ) -> Cursor<'a, K, V, B, C, S> {
        Cursor {
            tree: self,
            slab,
            stack: [(ptr::null_mut(), 0u16); MAX_DEPTH],
            stack_len: 0,
            started: false,
        }
    }

    /// Returns a cursor positioned at the given key.
    pub fn cursor_at<'a, S: SlabOps<BTreeNode<K, V, B>>>(
        &'a mut self,
        slab: &'a S,
        key: &K,
    ) -> Cursor<'a, K, V, B, C, S> {
        let mut cursor = Cursor {
            tree: self,
            slab,
            stack: [(ptr::null_mut(), 0u16); MAX_DEPTH],
            stack_len: 0,
            started: true,
        };
        if !cursor.tree.root.is_null() {
            init_lower_bound_stack::<K, V, B, C>(
                cursor.tree.root,
                key,
                &mut cursor.stack,
                &mut cursor.stack_len,
            );
        }
        cursor
    }

    // =========================================================================
    // Drain
    // =========================================================================

    /// Returns a draining iterator.
    pub fn drain<'a, S: SlabOps<BTreeNode<K, V, B>>>(
        &'a mut self,
        slab: &'a S,
    ) -> DrainBTree<'a, K, V, B, C, S> {
        DrainBTree { tree: self, slab }
    }

    // =========================================================================
    // Internal: find
    // =========================================================================

    fn find(&self, key: &K) -> Option<(NodePtr<K, V, B>, usize)> {
        let mut current = self.root;
        while !current.is_null() {
            // SAFETY: current is non-null and a valid tree node (root or child).
            let (idx, found) = unsafe { search_in_node::<K, V, B, C>(current, key) };
            if found {
                return Some((current, idx));
            }
            // SAFETY: current is a valid node.
            if unsafe { node_is_leaf(current) } {
                return None;
            }
            // SAFETY: current is a valid internal node, idx <= node.len.
            let next = unsafe { child_at(current, idx) };
            current = next;
        }
        None
    }

    // =========================================================================
    // Internal: remove logic
    // =========================================================================

    /// Removes the key-value at `idx` in `node`. If `node` is internal,
    /// replaces with the in-order predecessor and removes from the leaf.
    ///
    /// # Safety
    ///
    /// - `node` must be a valid B-tree node found by `remove_entry`'s
    ///   traversal from the root (each hop follows `children[idx]` of a
    ///   valid internal node).
    /// - `idx < node.len`, so keys[idx] and values[idx] are initialized
    ///   (the key was found at this position by `search_in_node`).
    /// - `path[0..path_len]` contains valid (parent, child_idx) pairs
    ///   collected during the downward traversal.
    unsafe fn remove_found(
        &mut self,
        slab: &impl SlabOps<BTreeNode<K, V, B>>,
        node: NodePtr<K, V, B>,
        idx: usize,
        path: &[(NodePtr<K, V, B>, usize); MAX_DEPTH],
        path_len: usize,
    ) -> (K, V) {
        // SAFETY: node is a valid B-tree node from the downward traversal; node_is_leaf reads the leaf flag.
        if unsafe { node_is_leaf(node) } {
            // SAFETY: idx < node.len, so take_kv reads initialized slots.
            // shift_left closes the gap and decrements len.
            let result = unsafe { take_kv(node, idx) };
            // SAFETY: node is a valid leaf; shift_left closes the gap at idx and decrements len.
            unsafe { shift_left(node, idx) };
            self.fixup_after_remove(slab, node, path, path_len);
            result
        } else {
            // Internal node: replace with in-order predecessor (rightmost
            // key in the left subtree), then remove the predecessor from
            // its leaf.
            let mut ext_path = *path;
            let mut ext_len = path_len;
            debug_assert!(ext_len < MAX_DEPTH);
            ext_path[ext_len] = (node, idx);
            ext_len += 1;

            // SAFETY: node is internal, so children[idx] is a valid non-null
            // child (B-tree invariant: internal node with len keys has len+1
            // children). We walk down rightmost children until we hit a leaf.
            let mut pred_node = unsafe { child_at(node, idx) };
            // SAFETY: pred_node is non-null — initially children[idx] of an internal node, then a valid child on each iteration.
            while !unsafe { node_is_leaf(pred_node) } {
                // SAFETY: pred_node is a valid internal node on this iteration.
                let plen = unsafe { node_len(pred_node) };
                debug_assert!(ext_len < MAX_DEPTH);
                ext_path[ext_len] = (pred_node, plen);
                ext_len += 1;
                // SAFETY: pred_node is internal with `plen` keys, so
                // children[plen] is the rightmost valid child pointer.
                pred_node = unsafe { child_at(pred_node, plen) };
            }

            // SAFETY: pred_node is a leaf with at least 1 key (B-tree min
            // occupancy). pred_idx = len-1 is the last initialized slot.
            let pred_idx = unsafe { node_len(pred_node) } - 1;
            // SAFETY: idx < node.len — take_kv reads the target key-value
            // to return. The slot at idx becomes uninitialized.
            let result = unsafe { take_kv(node, idx) };

            // SAFETY: pred_idx < pred_node.len, so keys[pred_idx] and
            // values[pred_idx] are initialized. assume_init_read moves
            // the values out; we immediately write replacements into node.
            let pred_k = unsafe { (*node_deref(pred_node)).keys[pred_idx].assume_init_read() };
            // SAFETY: same invariant as above; values[pred_idx] is initialized for pred_idx < pred_node.len.
            let pred_v = unsafe { (*node_deref(pred_node)).values[pred_idx].assume_init_read() };

            // SAFETY: node is valid, idx < node.len. We overwrite the
            // uninitialized slot (from take_kv above) with the predecessor.
            let int_node = unsafe { &mut *node_deref_mut(node) };
            int_node.keys[idx] = MaybeUninit::new(pred_k);
            int_node.values[idx] = MaybeUninit::new(pred_v);

            // SAFETY: pred_node is valid. Decrementing len logically removes
            // the last key-value (already moved out by assume_init_read).
            unsafe { (*node_deref_mut(pred_node)).len -= 1 };
            self.fixup_after_remove(slab, pred_node, &ext_path, ext_len);
            result
        }
    }

    /// Walks up the ancestor path after a removal, rebalancing any node
    /// that has fallen below the minimum key count (B/2 - 1).
    ///
    /// Strategy at each underflowed node:
    /// 1. If it's the root and empty: collapse (free or promote child).
    /// 2. Try to borrow from left sibling (rotate_right).
    /// 3. Try to borrow from right sibling (rotate_left).
    /// 4. Merge with a sibling, pulling the separator from the parent.
    ///    Then continue up to the parent (which lost a key).
    ///
    /// All path entries are valid (parent, child_idx) pairs collected
    /// during the downward search in `remove_entry` / `remove_found`.
    fn fixup_after_remove(
        &mut self,
        slab: &impl SlabOps<BTreeNode<K, V, B>>,
        mut node: NodePtr<K, V, B>,
        path: &[(NodePtr<K, V, B>, usize); MAX_DEPTH],
        path_len: usize,
    ) {
        let min = B / 2 - 1;
        let mut depth = path_len;

        loop {
            // SAFETY: node was either the leaf where we removed (valid from
            // the initial traversal) or a parent we walked up to. All nodes
            // in path[] were visited during the downward search and remain
            // valid (no nodes freed yet on this upward pass except children
            // of merge targets, which are below us).
            let len = unsafe { node_len(node) };

            if node == self.root {
                if len == 0 {
                    // SAFETY: node is the root with 0 keys; node_is_leaf reads the flag to decide how to collapse.
                    if unsafe { node_is_leaf(node) } {
                        // SAFETY: empty leaf root — tree is now empty.
                        // free_node drops 0 elements (len == 0) and frees
                        // the slab slot.
                        unsafe { free_node(node, slab) };
                        self.root = ptr::null_mut();
                        self.depth = 0;
                    } else {
                        // SAFETY: internal root with 0 keys has exactly 1
                        // child at children[0] (post-merge). Promote it.
                        let new_root = unsafe { child_at(node, 0) };
                        // SAFETY: node is the old root with 0 keys; free_node drops nothing and returns its slab slot.
                        unsafe { free_node(node, slab) };
                        self.root = new_root;
                        self.depth -= 1;
                    }
                }
                return;
            }

            if len >= min {
                return;
            }

            // SAFETY: depth > 0 here (node != root), so path[depth-1] is
            // a valid (parent, child_idx) pair from the downward traversal.
            let (parent, child_idx) = path[depth - 1];
            // SAFETY: parent is a valid node from path[], which holds valid traversal pointers.
            let parent_len = unsafe { node_len(parent) };

            // Try borrowing from left sibling.
            if child_idx > 0 {
                // SAFETY: parent is a valid internal node and child_idx-1
                // is a valid child index (child_idx > 0).
                let left = unsafe { child_at(parent, child_idx - 1) };
                // SAFETY: left is a valid node obtained from child_at on a valid parent.
                if unsafe { node_len(left) } > min {
                    // SAFETY: parent is valid, child_idx > 0, and left has more than min keys (checked above).
                    unsafe { Self::rotate_right(parent, child_idx) };
                    return;
                }
            }

            // Try borrowing from right sibling.
            if child_idx < parent_len {
                // SAFETY: child_idx < parent_len, so child_idx+1 <= parent_len
                // which is a valid child index for an internal node.
                let right = unsafe { child_at(parent, child_idx + 1) };
                // SAFETY: right is a valid node obtained from child_at on a valid parent.
                if unsafe { node_len(right) } > min {
                    // SAFETY: parent is valid, child_idx < parent_len, and right has more than min keys (checked above).
                    unsafe { Self::rotate_left(parent, child_idx) };
                    return;
                }
            }

            // Neither sibling can donate — merge with one of them.
            let merge_idx = if child_idx > 0 {
                child_idx - 1
            } else {
                child_idx
            };
            // SAFETY: merge_idx < parent_len (either child_idx-1 or
            // child_idx, both < parent_len since parent has enough children).
            unsafe { Self::merge_children(slab, parent, merge_idx) };

            node = parent;
            depth -= 1;
        }
    }

    /// B-tree right rotation: borrows from the left sibling through the parent.
    ///
    /// Moves the parent's separator key down into the deficient child (at
    /// position 0), and promotes the left sibling's last key into the
    /// parent. If internal, the left sibling's rightmost child pointer
    /// becomes the child's new leftmost child.
    ///
    /// # Safety
    ///
    /// - `parent` must be a valid internal node obtained from traversal.
    /// - `child_idx > 0` and `child_idx <= parent.len`, so both
    ///   `children[child_idx]` and `children[child_idx - 1]` are valid.
    /// - The left sibling must have more than minimum keys (checked by
    ///   `fixup_after_remove` before calling).
    /// - No aliasing: parent, child, and left are distinct slab-allocated
    ///   nodes (B-tree structure invariant).
    unsafe fn rotate_right(parent: NodePtr<K, V, B>, child_idx: usize) {
        // SAFETY: parent is a valid internal node per caller. children[child_idx]
        // and children[child_idx-1] are valid child pointers (child_idx > 0,
        // child_idx <= parent.len). All three are distinct slab allocations.
        let parent_node = unsafe { &mut *node_deref_mut(parent) };
        let child = parent_node.children[child_idx];
        let left = parent_node.children[child_idx - 1];
        // SAFETY: child is the valid pointer at parent.children[child_idx]; distinct slab allocation from parent.
        let child_node = unsafe { &mut *node_deref_mut(child) };
        // SAFETY: left is the valid pointer at parent.children[child_idx-1]; distinct slab allocation from parent and child.
        let left_node = unsafe { &mut *node_deref_mut(left) };
        let child_len = child_node.len as usize;
        let left_len = left_node.len as usize;
        let p_idx = child_idx - 1;

        // Shift child's keys/values right by 1 to make room at index 0.
        // SAFETY: child has child_len initialized keys/values at [0..child_len).
        // After shift, [1..child_len+1) are initialized. child_len < B-1
        // (child was deficient), so index child_len is within the array.
        if child_len > 0 {
            // SAFETY: child has child_len initialized keys/values at [0..child_len); child_len < B-1 so the shift destination is within bounds.
            unsafe {
                let kp = child_node.keys.as_mut_ptr();
                ptr::copy(kp.cast_const(), kp.add(1), child_len);
                let vp = child_node.values.as_mut_ptr();
                ptr::copy(vp.cast_const(), vp.add(1), child_len);
            }
        }
        if !child_node.leaf {
            // SAFETY: internal child has child_len+1 valid children at
            // [0..child_len]. Shift to [1..child_len+1]. child_len+1 < B
            // (deficient node), so destination is within bounds.
            unsafe {
                let cp = child_node.children.as_mut_ptr();
                ptr::copy(cp.cast_const(), cp.add(1), child_len + 1);
            }
        }

        // SAFETY: p_idx < parent.len (p_idx = child_idx - 1 < parent.len),
        // so keys[p_idx] and values[p_idx] are initialized. assume_init_read
        // moves the value out; we immediately write a replacement below.
        child_node.keys[0] =
            MaybeUninit::new(unsafe { parent_node.keys[p_idx].assume_init_read() });
        // SAFETY: same as above — p_idx < parent.len so values[p_idx] is initialized.
        child_node.values[0] =
            MaybeUninit::new(unsafe { parent_node.values[p_idx].assume_init_read() });
        if !child_node.leaf {
            // SAFETY: left is internal with left_len keys, so
            // children[left_len] is the rightmost valid child pointer.
            child_node.children[0] = left_node.children[left_len];
        }
        // SAFETY: left_len > min (caller checked), so left_len - 1 >= 0
        // and left.keys[left_len-1] is initialized. Promoting it into parent.
        parent_node.keys[p_idx] =
            MaybeUninit::new(unsafe { left_node.keys[left_len - 1].assume_init_read() });
        // SAFETY: same as above — left.values[left_len-1] is initialized (left_len > min).
        parent_node.values[p_idx] =
            MaybeUninit::new(unsafe { left_node.values[left_len - 1].assume_init_read() });

        child_node.len += 1;
        left_node.len -= 1;
    }

    /// B-tree left rotation: borrows from the right sibling through the parent.
    ///
    /// Moves the parent's separator key down to the end of the deficient
    /// child, and promotes the right sibling's first key into the parent.
    /// If internal, the right sibling's leftmost child pointer moves to
    /// the child's new rightmost position.
    ///
    /// # Safety
    ///
    /// - `parent` must be a valid internal node obtained from traversal.
    /// - `child_idx < parent.len`, so both `children[child_idx]` and
    ///   `children[child_idx + 1]` are valid child pointers.
    /// - The right sibling must have more than minimum keys (checked by
    ///   `fixup_after_remove` before calling).
    /// - No aliasing: parent, child, and right are distinct slab allocations.
    unsafe fn rotate_left(parent: NodePtr<K, V, B>, child_idx: usize) {
        // SAFETY: parent is a valid internal node. children[child_idx] and
        // children[child_idx+1] are valid (child_idx < parent.len).
        let parent_node = unsafe { &mut *node_deref_mut(parent) };
        let child = parent_node.children[child_idx];
        let right = parent_node.children[child_idx + 1];
        // SAFETY: child is the valid pointer at parent.children[child_idx]; distinct slab allocation from parent.
        let child_node = unsafe { &mut *node_deref_mut(child) };
        // SAFETY: right is the valid pointer at parent.children[child_idx+1]; distinct slab allocation from parent and child.
        let right_node = unsafe { &mut *node_deref_mut(right) };
        let child_len = child_node.len as usize;
        let right_len = right_node.len as usize;
        let p_idx = child_idx;

        // SAFETY: p_idx < parent.len, so keys[p_idx] is initialized.
        // assume_init_read moves the value; we write a replacement below.
        // child_len < B-1 (child is deficient), so keys[child_len] is
        // within the array bounds.
        child_node.keys[child_len] =
            MaybeUninit::new(unsafe { parent_node.keys[p_idx].assume_init_read() });
        // SAFETY: same as above — p_idx < parent.len so values[p_idx] is initialized.
        child_node.values[child_len] =
            MaybeUninit::new(unsafe { parent_node.values[p_idx].assume_init_read() });
        if !child_node.leaf {
            // SAFETY: right is internal, children[0] is a valid pointer.
            // child_len + 1 < B (deficient child), so the destination is
            // within bounds.
            child_node.children[child_len + 1] = right_node.children[0];
        }
        // SAFETY: right_len > min (caller checked), so right.keys[0] is
        // initialized. Promoting it into the parent at p_idx.
        parent_node.keys[p_idx] =
            MaybeUninit::new(unsafe { right_node.keys[0].assume_init_read() });
        // SAFETY: same as above — right.values[0] is initialized (right_len > min >= 1).
        parent_node.values[p_idx] =
            MaybeUninit::new(unsafe { right_node.values[0].assume_init_read() });

        // Shift right sibling's keys/values left by 1 to close the gap.
        // SAFETY: right_len > 1 (right_len > min >= 1), so [1..right_len)
        // has right_len-1 initialized elements. ptr::copy handles the
        // overlapping source/dest correctly.
        if right_len > 1 {
            // SAFETY: right_len > 1 so [1..right_len) has right_len-1 initialized elements; ptr::copy handles overlapping regions.
            unsafe {
                let kp = right_node.keys.as_mut_ptr();
                ptr::copy(kp.add(1).cast_const(), kp, right_len - 1);
                let vp = right_node.values.as_mut_ptr();
                ptr::copy(vp.add(1).cast_const(), vp, right_len - 1);
            }
        }
        if !right_node.leaf {
            // SAFETY: internal right has right_len+1 children at [0..right_len].
            // Shift [1..right_len] to [0..right_len-1]. right_len elements.
            unsafe {
                let cp = right_node.children.as_mut_ptr();
                ptr::copy(cp.add(1).cast_const(), cp, right_len);
            }
        }

        child_node.len += 1;
        right_node.len -= 1;
    }

    /// Merges children at `merge_idx` and `merge_idx + 1` with the parent's
    /// separator key. The right child is freed after merging into the left.
    ///
    /// After merge, left has: [left keys] + [separator] + [right keys],
    /// totaling left_len + 1 + right_len = 2*min + 1 = B-1 keys (full node).
    ///
    /// # Safety
    ///
    /// - `parent` must be a valid internal node from the traversal path.
    /// - `merge_idx < parent.len`, so `children[merge_idx]` (left) and
    ///   `children[merge_idx + 1]` (right) are both valid child pointers.
    /// - Both children have exactly minimum keys (B/2 - 1). This ensures
    ///   the merged result fits in a single node (2*min + 1 == B-1).
    /// - No aliasing: parent, left, and right are distinct slab allocations.
    unsafe fn merge_children(
        slab: &impl SlabOps<BTreeNode<K, V, B>>,
        parent: NodePtr<K, V, B>,
        merge_idx: usize,
    ) {
        // SAFETY: parent is valid internal node. children[merge_idx] and
        // children[merge_idx+1] are valid (merge_idx < parent.len).
        let parent_node = unsafe { &*node_deref(parent) };
        let left = parent_node.children[merge_idx];
        let right = parent_node.children[merge_idx + 1];
        // SAFETY: left and right are distinct slab-allocated nodes. We take
        // &mut of left (will be modified) and & of right (read-only, then freed).
        let left_node = unsafe { &mut *node_deref_mut(left) };
        // SAFETY: right is the valid pointer at parent.children[merge_idx+1]; distinct slab allocation from parent and left.
        let right_node = unsafe { &*node_deref(right) };
        let left_len = left_node.len as usize;
        let right_len = right_node.len as usize;

        // SAFETY: merge_idx < parent.len, so keys[merge_idx] is initialized.
        // assume_init_read moves the separator into left at index left_len.
        // left_len == min < B-1, so keys[left_len] is within array bounds.
        left_node.keys[left_len] =
            MaybeUninit::new(unsafe { (*node_deref(parent)).keys[merge_idx].assume_init_read() });
        // SAFETY: same as above — merge_idx < parent.len so values[merge_idx] is initialized.
        left_node.values[left_len] =
            MaybeUninit::new(unsafe { (*node_deref(parent)).values[merge_idx].assume_init_read() });

        // SAFETY: right has right_len initialized keys/values at [0..right_len).
        // Destination starts at left_len + 1. Total: left_len + 1 + right_len
        // == 2*min + 1 == B-1, so destination indices are within [0, B-1).
        // Source and destination are in different nodes — no overlap.
        if right_len > 0 {
            // SAFETY: right has right_len initialized keys/values at [0..right_len); destination in left starts at left_len+1; nodes are distinct so no overlap.
            unsafe {
                ptr::copy_nonoverlapping(
                    right_node.keys.as_ptr(),
                    left_node.keys.as_mut_ptr().add(left_len + 1),
                    right_len,
                );
                ptr::copy_nonoverlapping(
                    right_node.values.as_ptr(),
                    left_node.values.as_mut_ptr().add(left_len + 1),
                    right_len,
                );
            }
        }
        if !left_node.leaf {
            // SAFETY: right is internal with right_len+1 valid children.
            // Destination starts at left_len + 1. Total children in merged
            // node: left_len + 1 + right_len + 1 == B, which fits exactly
            // in the children array of size B.
            unsafe {
                ptr::copy_nonoverlapping(
                    right_node.children.as_ptr(),
                    left_node.children.as_mut_ptr().add(left_len + 1),
                    right_len + 1,
                );
            }
        }

        left_node.len = (left_len + 1 + right_len) as u16;

        // SAFETY: right was obtained from Slot::into_raw() during a prior
        // insert or split. All its key/value data has been moved to left
        // (via copy_nonoverlapping above), so right's slots are logically
        // uninitialized. Slot::from_raw reconstitutes the handle for freeing.
        // free_slot does NOT run drop on keys/values (they were moved, not copied).
        let slot = unsafe { Slot::from_raw(right) };
        slab.free_slot(slot);
        // SAFETY: merge_idx < parent.len. shift_left removes the separator
        // at merge_idx and shifts remaining keys/children left by one.
        unsafe { shift_left(parent, merge_idx) };
    }

    // =========================================================================
    // Internal: insert helpers
    // =========================================================================

    #[allow(clippy::type_complexity)]
    fn try_insert_inner(
        &mut self,
        slab: &bounded::Slab<BTreeNode<K, V, B>>,
        key: K,
        value: V,
    ) -> Result<(*mut V, Option<V>), Full<(K, V)>> {
        if self.root.is_null() {
            let mut leaf = BTreeNode::new_leaf();
            leaf.keys[0] = MaybeUninit::new(key);
            leaf.values[0] = MaybeUninit::new(value);
            leaf.len = 1;
            match slab.try_alloc(leaf) {
                Ok(slot) => {
                    let ptr = slot.into_raw();
                    self.root = ptr;
                    self.len += 1;
                    self.depth = 0;
                    // SAFETY: ptr is freshly allocated with len=1, so values[0] is initialized.
                    let val_ptr = unsafe { (*node_deref_mut(ptr)).values[0].as_mut_ptr() };
                    return Ok((val_ptr, None));
                }
                Err(full) => {
                    let node = full.into_inner();
                    // SAFETY: we initialized keys[0] and values[0] above before try_alloc.
                    // The alloc failed, returning the node. Read back the initialized slots.
                    let k = unsafe { node.keys[0].assume_init_read() };
                    // SAFETY: same as above — values[0] was initialized before the failed alloc.
                    let v = unsafe { node.values[0].assume_init_read() };
                    return Err(Full((k, v)));
                }
            }
        }

        // SAFETY: self.root is non-null (checked above). node_len reads the len field.
        if unsafe { node_len(self.root) } == B - 1 {
            let new_root = match slab.try_alloc(BTreeNode::new_internal()) {
                Ok(slot) => slot.into_raw(),
                Err(_) => return Err(Full((key, value))),
            };
            // SAFETY: new_root is freshly allocated. Set its first child to old root.
            unsafe { (*node_deref_mut(new_root)).children[0] = self.root };
            let old_root = self.root;
            self.root = new_root;

            // SAFETY: old_root is a valid node.
            let right_node = if unsafe { node_is_leaf(old_root) } {
                BTreeNode::new_leaf()
            } else {
                BTreeNode::new_internal()
            };
            let right = if let Ok(slot) = slab.try_alloc(right_node) {
                slot.into_raw()
            } else {
                self.root = old_root;
                // SAFETY: new_root was obtained from Slot::into_raw() above.
                let slot = unsafe { Slot::from_raw(new_root) };
                slab.free(slot);
                return Err(Full((key, value)));
            };
            // SAFETY: new_root is a valid internal node with 1 child. old_root
            // (child 0) is full. right is freshly allocated empty node.
            unsafe { split_child_core(new_root, 0, right) };
            self.depth += 1;
        }

        let mut current = self.root;
        loop {
            // SAFETY: current is non-null and a valid tree node.
            let (idx, found) = unsafe { search_in_node::<K, V, B, C>(current, &key) };
            if found {
                // SAFETY: idx < node.len (found), current is valid; &mut self exclusivity.
                let existing = unsafe { value_at_mut(current, idx) };
                let old = std::mem::replace(existing, value);
                let val_ptr = existing as *mut V;
                return Ok((val_ptr, Some(old)));
            }
            // SAFETY: current is a valid node.
            if unsafe { node_is_leaf(current) } {
                // SAFETY: current is a valid leaf with room (root was split if full).
                unsafe { shift_right(current, idx) };
                // SAFETY: current is a valid leaf node; &mut self ensures no aliasing.
                let node = unsafe { &mut *node_deref_mut(current) };
                node.keys[idx] = MaybeUninit::new(key);
                node.values[idx] = MaybeUninit::new(value);
                node.len += 1;
                self.len += 1;
                let val_ptr = node.values[idx].as_mut_ptr();
                return Ok((val_ptr, None));
            }

            let mut child_idx = idx;
            // SAFETY: current is a valid internal node, child_idx <= node.len.
            let child = unsafe { child_at(current, child_idx) };
            // SAFETY: child is a valid node.
            if unsafe { node_len(child) } == B - 1 {
                // SAFETY: child is a valid node.
                let right = match slab.try_alloc(if unsafe { node_is_leaf(child) } {
                    BTreeNode::new_leaf()
                } else {
                    BTreeNode::new_internal()
                }) {
                    Ok(slot) => slot.into_raw(),
                    Err(_) => return Err(Full((key, value))),
                };
                // SAFETY: current is non-full (proactive split ensures room),
                // child at child_idx is full, right is freshly allocated.
                unsafe { split_child_core(current, child_idx, right) };
                // SAFETY: child_idx < current.len after split promoted the median.
                let median = unsafe { key_at(current, child_idx) };
                match C::cmp(&key, median) {
                    Ordering::Equal => {
                        // SAFETY: child_idx < node.len; current is valid.
                        let existing = unsafe { value_at_mut(current, child_idx) };
                        let old = std::mem::replace(existing, value);
                        let val_ptr = existing as *mut V;
                        return Ok((val_ptr, Some(old)));
                    }
                    Ordering::Greater => child_idx += 1,
                    Ordering::Less => {}
                }
            }
            // SAFETY: current is a valid internal node, child_idx <= node.len.
            current = unsafe { child_at(current, child_idx) };
        }
    }

    fn insert_inner(
        &mut self,
        slab: &nexus_slab::unbounded::Slab<BTreeNode<K, V, B>>,
        key: K,
        value: V,
    ) -> (*mut V, Option<V>) {
        if self.root.is_null() {
            let mut leaf = BTreeNode::new_leaf();
            leaf.keys[0] = MaybeUninit::new(key);
            leaf.values[0] = MaybeUninit::new(value);
            leaf.len = 1;
            let slot = slab.alloc(leaf);
            let ptr = slot.into_raw();
            self.root = ptr;
            self.len += 1;
            self.depth = 0;
            // SAFETY: ptr is freshly allocated with len=1, so values[0] is initialized.
            let val_ptr = unsafe { (*node_deref_mut(ptr)).values[0].as_mut_ptr() };
            return (val_ptr, None);
        }

        // SAFETY: self.root is non-null (checked above). node_len reads the len field.
        if unsafe { node_len(self.root) } == B - 1 {
            let new_root = slab.alloc(BTreeNode::new_internal()).into_raw();
            // SAFETY: new_root is freshly allocated. Set its first child to old root.
            unsafe { (*node_deref_mut(new_root)).children[0] = self.root };
            let old_root = self.root;
            self.root = new_root;
            // SAFETY: old_root is a valid node.
            let right = slab
                .alloc(if unsafe { node_is_leaf(old_root) } {
                    BTreeNode::new_leaf()
                } else {
                    BTreeNode::new_internal()
                })
                .into_raw();
            // SAFETY: new_root has 1 child (old_root, which is full), right is
            // freshly allocated empty node.
            unsafe { split_child_core(new_root, 0, right) };
            self.depth += 1;
        }

        let mut current = self.root;
        loop {
            // SAFETY: current is non-null and a valid tree node.
            let (idx, found) = unsafe { search_in_node::<K, V, B, C>(current, &key) };
            if found {
                // SAFETY: idx < node.len (found), current is valid; &mut self exclusivity.
                let existing = unsafe { value_at_mut(current, idx) };
                let old = std::mem::replace(existing, value);
                let val_ptr = existing as *mut V;
                return (val_ptr, Some(old));
            }
            // SAFETY: current is a valid node.
            if unsafe { node_is_leaf(current) } {
                // SAFETY: current is a valid leaf with room (proactive split).
                unsafe { shift_right(current, idx) };
                // SAFETY: current is a valid leaf node; &mut self ensures no aliasing.
                let node = unsafe { &mut *node_deref_mut(current) };
                node.keys[idx] = MaybeUninit::new(key);
                node.values[idx] = MaybeUninit::new(value);
                node.len += 1;
                self.len += 1;
                let val_ptr = node.values[idx].as_mut_ptr();
                return (val_ptr, None);
            }

            let mut child_idx = idx;
            // SAFETY: current is a valid internal node, child_idx <= node.len.
            let child = unsafe { child_at(current, child_idx) };
            // SAFETY: child is a valid node.
            if unsafe { node_len(child) } == B - 1 {
                // SAFETY: child is a valid node.
                let right = slab
                    .alloc(if unsafe { node_is_leaf(child) } {
                        BTreeNode::new_leaf()
                    } else {
                        BTreeNode::new_internal()
                    })
                    .into_raw();
                // SAFETY: current is non-full, child at child_idx is full,
                // right is freshly allocated.
                unsafe { split_child_core(current, child_idx, right) };
                // SAFETY: child_idx < current.len after split promoted the median.
                let median = unsafe { key_at(current, child_idx) };
                match C::cmp(&key, median) {
                    Ordering::Equal => {
                        // SAFETY: child_idx < node.len; current is valid.
                        let existing = unsafe { value_at_mut(current, child_idx) };
                        let old = std::mem::replace(existing, value);
                        let val_ptr = existing as *mut V;
                        return (val_ptr, Some(old));
                    }
                    Ordering::Greater => child_idx += 1,
                    Ordering::Less => {}
                }
            }
            // SAFETY: current is a valid internal node, child_idx <= node.len.
            current = unsafe { child_at(current, child_idx) };
        }
    }

    // =========================================================================
    // Internal: range/iterator stack helpers
    // =========================================================================

    fn lower_bound_pos(&self, key: &K) -> (NodePtr<K, V, B>, u16) {
        let mut result: (NodePtr<K, V, B>, u16) = (ptr::null_mut(), 0);
        let mut current = self.root;
        while !current.is_null() {
            // SAFETY: current is non-null and a valid tree node (root or child).
            let (idx, found) = unsafe { search_in_node::<K, V, B, C>(current, key) };
            if found {
                return (current, idx as u16);
            }
            // SAFETY: current is a valid node.
            if unsafe { node_is_leaf(current) } {
                // SAFETY: current is a valid leaf node; node_len reads the len field.
                if idx < unsafe { node_len(current) } {
                    return (current, idx as u16);
                }
                return result;
            }
            // SAFETY: current is a valid internal node; node_len reads the len field.
            if idx < unsafe { node_len(current) } {
                result = (current, idx as u16);
            }
            // SAFETY: current is a valid internal node, idx <= node.len.
            current = unsafe { child_at(current, idx) };
        }
        result
    }

    fn upper_bound_pos(&self, key: &K) -> (NodePtr<K, V, B>, u16) {
        let mut result: (NodePtr<K, V, B>, u16) = (ptr::null_mut(), 0);
        let mut current = self.root;
        while !current.is_null() {
            // SAFETY: current is non-null and a valid tree node (root or child).
            let (idx, found) = unsafe { search_in_node::<K, V, B, C>(current, key) };
            if found {
                // SAFETY: current is a valid node.
                if unsafe { node_is_leaf(current) } {
                    // SAFETY: current is a valid leaf node; node_len reads the len field.
                    if idx + 1 < unsafe { node_len(current) } {
                        return (current, (idx + 1) as u16);
                    }
                    return result;
                }
                // SAFETY: current is internal, idx+1 <= node.len (found at idx).
                let mut c = unsafe { child_at(current, idx + 1) };
                // SAFETY: c is a valid child node; loop descends leftmost children.
                while !unsafe { node_is_leaf(c) } {
                    // SAFETY: c is an internal node; child_at(c, 0) is the leftmost valid child.
                    c = unsafe { child_at(c, 0) };
                }
                return (c, 0);
            }
            // SAFETY: current is a valid node.
            if unsafe { node_is_leaf(current) } {
                // SAFETY: current is a valid leaf node; node_len reads the len field.
                if idx < unsafe { node_len(current) } {
                    return (current, idx as u16);
                }
                return result;
            }
            // SAFETY: current is a valid internal node; node_len reads the len field.
            if idx < unsafe { node_len(current) } {
                result = (current, idx as u16);
            }
            // SAFETY: current is a valid internal node, idx <= node.len.
            current = unsafe { child_at(current, idx) };
        }
        result
    }

    // =========================================================================
    // Invariant verification
    // =========================================================================

    /// Verifies all B-tree invariants.
    #[doc(hidden)]
    pub fn verify_invariants(&self) {
        if self.root.is_null() {
            assert_eq!(self.len, 0);
            assert_eq!(self.depth, 0);
            return;
        }
        let min = B / 2 - 1;
        let mut leaf_depth: Option<usize> = None;
        let mut count = 0usize;
        Self::verify_subtree(
            self.root,
            true,
            min,
            0,
            &mut leaf_depth,
            &mut count,
            None,
            None,
        );
        assert_eq!(count, self.len);
        if let Some(ld) = leaf_depth {
            assert_eq!(ld, self.depth);
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn verify_subtree(
        ptr: NodePtr<K, V, B>,
        is_root: bool,
        min: usize,
        depth: usize,
        leaf_depth: &mut Option<usize>,
        count: &mut usize,
        lower: Option<&K>,
        upper: Option<&K>,
    ) {
        // SAFETY: ptr is non-null — root (verified non-null in verify_invariants)
        // or a child pointer from a valid parent node (checked non-null above).
        let node = unsafe { &*node_deref(ptr) };
        let len = node.len as usize;
        assert!(len < B);
        if !is_root {
            assert!(len >= min);
        }
        assert!(!(is_root && !node.leaf && len == 0));

        for i in 1..len {
            // SAFETY: keys[i-1] and keys[i] are initialized for i < len.
            let prev = unsafe { node.keys[i - 1].assume_init_ref() };
            // SAFETY: keys[i] is initialized for i < len (same reasoning as above).
            let curr = unsafe { node.keys[i].assume_init_ref() };
            assert!(C::cmp(prev, curr) == Ordering::Less);
        }
        if let Some(lo) = lower {
            // SAFETY: keys[0] is initialized (len > 0, checked via min occupancy).
            let first = unsafe { node.keys[0].assume_init_ref() };
            assert!(C::cmp(first, lo) == Ordering::Greater);
        }
        if let Some(hi) = upper {
            // SAFETY: keys[len-1] is initialized for len > 0.
            let last = unsafe { node.keys[len - 1].assume_init_ref() };
            assert!(C::cmp(last, hi) == Ordering::Less);
        }

        *count += len;

        if node.leaf {
            match *leaf_depth {
                None => *leaf_depth = Some(depth),
                Some(expected) => assert_eq!(depth, expected),
            }
        } else {
            for i in 0..=len {
                assert!(!node.children[i].is_null());
            }
            for i in 0..=len {
                let lo = if i > 0 {
                    // SAFETY: keys[i-1] is initialized for i <= len.
                    Some(unsafe { node.keys[i - 1].assume_init_ref() })
                } else {
                    lower
                };
                let hi = if i < len {
                    // SAFETY: keys[i] is initialized for i < len.
                    Some(unsafe { node.keys[i].assume_init_ref() })
                } else {
                    upper
                };
                Self::verify_subtree(
                    node.children[i],
                    false,
                    min,
                    depth + 1,
                    leaf_depth,
                    count,
                    lo,
                    hi,
                );
            }
        }
    }
}

// =============================================================================
// new — Natural-specific
// =============================================================================

impl<K, V, const B: usize> BTree<K, V, B> {
    /// Creates a new empty B-tree with natural (`Ord`) key ordering.
    pub fn new() -> Self {
        assert!(B >= 4, "B must be >= 4");
        assert!(B.is_multiple_of(2), "B must be even");
        assert!(
            std::mem::size_of::<BTreeNode<K, V, B>>() <= 1024,
            "BTreeNode exceeds 1024 bytes"
        );
        BTree {
            root: ptr::null_mut(),
            len: 0,
            depth: 0,

            _marker: PhantomData,
        }
    }
}

impl<K, V, const B: usize> Default for BTree<K, V, B> {
    fn default() -> Self {
        Self::new()
    }
}

// BTree does NOT implement Drop in release. The user must call clear() with
// the slab to release nodes. In debug builds, we panic to catch slot leaks.
#[cfg(debug_assertions)]
impl<K, V, const B: usize, C> Drop for BTree<K, V, B, C> {
    #[allow(clippy::manual_assert)]
    fn drop(&mut self) {
        if self.len > 0 && !std::thread::panicking() {
            panic!(
                "BTree dropped with {} elements without calling clear(). \
                 This leaks slab slots. Call tree.clear(&slab) before dropping.",
                self.len
            );
        }
    }
}

// =============================================================================
// Unconstrained methods
// =============================================================================

impl<K, V, const B: usize, C> BTree<K, V, B, C> {
    /// Creates a new empty B-tree with a custom comparator.
    #[allow(unused_variables, clippy::needless_pass_by_value)]
    pub fn with_comparator(comparator: C) -> Self {
        assert!(B >= 4);
        assert!(B.is_multiple_of(2));
        assert!(std::mem::size_of::<BTreeNode<K, V, B>>() <= 1024);
        BTree {
            root: ptr::null_mut(),
            len: 0,
            depth: 0,

            _marker: PhantomData,
        }
    }

    /// Returns the number of elements.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the first (smallest) key-value pair.
    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        if self.root.is_null() {
            return None;
        }
        let mut current = self.root;
        loop {
            // SAFETY: current is non-null (root checked above, then valid children).
            if unsafe { node_is_leaf(current) } {
                // SAFETY: current is a valid leaf with at least 1 key.
                return Some(unsafe { (key_at(current, 0), value_at(current, 0)) });
            }
            // SAFETY: current is a valid internal node, child 0 exists.
            current = unsafe { child_at(current, 0) };
        }
    }

    /// Returns the last (largest) key-value pair.
    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        if self.root.is_null() {
            return None;
        }
        let mut current = self.root;
        loop {
            // SAFETY: current is non-null (root checked above, then valid children).
            let len = unsafe { node_len(current) };
            // SAFETY: current is a valid node; node_is_leaf reads the leaf flag.
            if unsafe { node_is_leaf(current) } {
                // SAFETY: current is a valid leaf with at least 1 key; len-1 is valid.
                return Some(unsafe { (key_at(current, len - 1), value_at(current, len - 1)) });
            }
            // SAFETY: current is a valid internal node, child at index len exists.
            current = unsafe { child_at(current, len) };
        }
    }

    /// Removes all nodes.
    pub fn clear(&mut self, slab: &impl SlabOps<BTreeNode<K, V, B>>) {
        if !self.root.is_null() {
            // SAFETY: self.root is non-null and a valid tree root.
            unsafe { Self::clear_subtree(self.root, slab) };
        }
        self.root = ptr::null_mut();
        self.len = 0;
        self.depth = 0;
    }

    /// Recursively frees all nodes in the subtree rooted at `ptr`.
    ///
    /// Post-order traversal: children are freed before their parent, so
    /// no dangling pointers are dereferenced. `free_node` drops all
    /// initialized keys/values in the node, then returns the slab slot.
    ///
    /// # Safety
    ///
    /// `ptr` must be a valid non-null B-tree node obtained from
    /// `Slot::into_raw()` during insert/split. The entire subtree
    /// must be exclusively owned (no concurrent readers/writers).
    unsafe fn clear_subtree(ptr: NodePtr<K, V, B>, slab: &impl SlabOps<BTreeNode<K, V, B>>) {
        // SAFETY: ptr is a valid node per caller contract (root from self.root,
        // or a child pointer from a valid parent node).
        let node = unsafe { &*node_deref(ptr) };
        let len = node.len as usize;
        if !node.leaf {
            // SAFETY: an internal node with `len` keys has `len + 1` valid
            // children at indices [0..=len]. Each child was stored via
            // split_child_core or root init, pointing to occupied SlotCells.
            for i in 0..=len {
                let child = node.children[i];
                if !child.is_null() {
                    // SAFETY: child is a valid non-null node pointer from this internal node; exclusively owned.
                    unsafe { Self::clear_subtree(child, slab) };
                }
            }
        }
        // SAFETY: all children freed above (post-order). free_node drops
        // keys[0..len] and values[0..len] (all initialized), then frees
        // the slab slot via Slot::from_raw.
        unsafe { free_node(ptr, slab) };
    }
}

// Note: BTree does NOT implement Drop.

impl<K: fmt::Debug, V: fmt::Debug, const B: usize, C: Compare<K>> fmt::Debug for BTree<K, V, B, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

// =============================================================================
// Iterator stack helpers
// =============================================================================

fn push_leftmost_path<K, V, const B: usize>(
    mut node: NodePtr<K, V, B>,
    stack: &mut [(NodePtr<K, V, B>, u16); MAX_DEPTH],
    stack_len: &mut usize,
) {
    loop {
        debug_assert!(*stack_len < MAX_DEPTH);
        stack[*stack_len] = (node, 0);
        *stack_len += 1;
        // SAFETY: node is non-null (initially from caller, then valid children).
        if unsafe { node_is_leaf(node) } {
            return;
        }
        // SAFETY: node is a valid internal node, child 0 exists.
        node = unsafe { child_at(node, 0) };
    }
}

fn init_lower_bound_stack<K, V, const B: usize, C: Compare<K>>(
    root: NodePtr<K, V, B>,
    key: &K,
    stack: &mut [(NodePtr<K, V, B>, u16); MAX_DEPTH],
    stack_len: &mut usize,
) {
    let mut current = root;
    while !current.is_null() {
        // SAFETY: current is non-null and a valid tree node (root or child).
        let (idx, found) = unsafe { search_in_node::<K, V, B, C>(current, key) };
        if found {
            stack[*stack_len] = (current, idx as u16);
            *stack_len += 1;
            return;
        }
        // SAFETY: current is a valid node.
        if unsafe { node_is_leaf(current) } {
            // SAFETY: current is a valid leaf node; node_len reads the len field.
            if idx < unsafe { node_len(current) } {
                stack[*stack_len] = (current, idx as u16);
                *stack_len += 1;
            }
            return;
        }
        // SAFETY: current is a valid internal node; node_len reads the len field.
        if idx < unsafe { node_len(current) } {
            stack[*stack_len] = (current, idx as u16);
            *stack_len += 1;
        }
        // SAFETY: current is a valid internal node, idx <= node.len.
        current = unsafe { child_at(current, idx) };
    }
}

fn init_upper_bound_stack<K, V, const B: usize, C: Compare<K>>(
    root: NodePtr<K, V, B>,
    key: &K,
    stack: &mut [(NodePtr<K, V, B>, u16); MAX_DEPTH],
    stack_len: &mut usize,
) {
    let mut current = root;
    while !current.is_null() {
        // SAFETY: current is non-null and a valid tree node (root or child).
        let (idx, found) = unsafe { search_in_node::<K, V, B, C>(current, key) };
        if found {
            // SAFETY: current is a valid node.
            if unsafe { node_is_leaf(current) } {
                // SAFETY: current is a valid leaf node; node_len reads the len field.
                if idx + 1 < unsafe { node_len(current) } {
                    stack[*stack_len] = (current, (idx + 1) as u16);
                    *stack_len += 1;
                }
            } else {
                stack[*stack_len] = (current, (idx + 1) as u16);
                *stack_len += 1;
                // SAFETY: current is internal, idx+1 <= node.len.
                let child = unsafe { child_at(current, idx + 1) };
                push_leftmost_path(child, stack, stack_len);
            }
            return;
        }
        // SAFETY: current is a valid node.
        if unsafe { node_is_leaf(current) } {
            // SAFETY: current is a valid leaf node; node_len reads the len field.
            if idx < unsafe { node_len(current) } {
                stack[*stack_len] = (current, idx as u16);
                *stack_len += 1;
            }
            return;
        }
        // SAFETY: current is a valid internal node; node_len reads the len field.
        if idx < unsafe { node_len(current) } {
            stack[*stack_len] = (current, idx as u16);
            *stack_len += 1;
        }
        // SAFETY: current is a valid internal node, idx <= node.len.
        current = unsafe { child_at(current, idx) };
    }
}

fn advance_stack<K, V, const B: usize>(
    stack: &mut [(NodePtr<K, V, B>, u16); MAX_DEPTH],
    stack_len: &mut usize,
) -> Option<(NodePtr<K, V, B>, usize)> {
    while *stack_len > 0 {
        let (node, idx) = stack[*stack_len - 1];
        // SAFETY: node is a valid tree node pushed during traversal.
        if (idx as usize) < unsafe { node_len(node) } {
            break;
        }
        *stack_len -= 1;
    }
    if *stack_len == 0 {
        return None;
    }
    let (node, idx) = stack[*stack_len - 1];
    let i = idx as usize;
    stack[*stack_len - 1].1 = (i + 1) as u16;
    // SAFETY: node is a valid tree node from the traversal stack.
    if !unsafe { node_is_leaf(node) } {
        // SAFETY: node is internal, i+1 <= node.len (we just yielded key at i).
        let child = unsafe { child_at(node, i + 1) };
        push_leftmost_path(child, stack, stack_len);
    }
    Some((node, i))
}

fn advance_stack_range<K, V, const B: usize>(
    stack: &mut [(NodePtr<K, V, B>, u16); MAX_DEPTH],
    stack_len: &mut usize,
    end_node: NodePtr<K, V, B>,
    end_idx: u16,
) -> Option<(NodePtr<K, V, B>, usize)> {
    while *stack_len > 0 {
        let (node, idx) = stack[*stack_len - 1];
        // SAFETY: node is a valid tree node pushed during traversal.
        if (idx as usize) < unsafe { node_len(node) } {
            break;
        }
        *stack_len -= 1;
    }
    if *stack_len == 0 {
        return None;
    }
    let (node, idx) = stack[*stack_len - 1];
    if !end_node.is_null() && node == end_node && idx == end_idx {
        *stack_len = 0;
        return None;
    }
    let i = idx as usize;
    stack[*stack_len - 1].1 = (i + 1) as u16;
    // SAFETY: node is a valid tree node from the traversal stack.
    if !unsafe { node_is_leaf(node) } {
        // SAFETY: node is internal, i+1 <= node.len.
        let child = unsafe { child_at(node, i + 1) };
        push_leftmost_path(child, stack, stack_len);
    }
    Some((node, i))
}

// =============================================================================
// Iterators
// =============================================================================

/// Iterator over `(&K, &V)` pairs in sorted order.
pub struct Iter<'a, K, V, const B: usize> {
    stack: [(NodePtr<K, V, B>, u16); MAX_DEPTH],
    stack_len: usize,
    remaining: usize,
    _marker: PhantomData<&'a ()>,
}

impl<'a, K: 'a, V: 'a, const B: usize> Iterator for Iter<'a, K, V, B> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        let (node, idx) = advance_stack(&mut self.stack, &mut self.stack_len)?;
        self.remaining -= 1;
        // SAFETY: advance_stack returns a valid (node, idx) where idx < node.len.
        Some(unsafe { (key_at(node, idx), value_at(node, idx)) })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}
impl<'a, K: 'a, V: 'a, const B: usize> ExactSizeIterator for Iter<'a, K, V, B> {}

impl<'a, K: 'a, V, const B: usize, C: Compare<K>> IntoIterator for &'a BTree<K, V, B, C> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V, B>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K: 'a, V, const B: usize, C: Compare<K>> IntoIterator for &'a mut BTree<K, V, B, C> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V, B>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// Iterator over keys.
pub struct Keys<'a, K, V, const B: usize> {
    inner: Iter<'a, K, V, B>,
}
impl<'a, K: 'a, V: 'a, const B: usize> Iterator for Keys<'a, K, V, B> {
    type Item = &'a K;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}
impl<'a, K: 'a, V: 'a, const B: usize> ExactSizeIterator for Keys<'a, K, V, B> {}

/// Iterator over values.
pub struct Values<'a, K, V, const B: usize> {
    inner: Iter<'a, K, V, B>,
}
impl<'a, K: 'a, V: 'a, const B: usize> Iterator for Values<'a, K, V, B> {
    type Item = &'a V;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}
impl<'a, K: 'a, V: 'a, const B: usize> ExactSizeIterator for Values<'a, K, V, B> {}

/// Mutable iterator.
pub struct IterMut<'a, K, V, const B: usize> {
    stack: [(NodePtr<K, V, B>, u16); MAX_DEPTH],
    stack_len: usize,
    remaining: usize,
    _marker: PhantomData<&'a mut ()>,
}
impl<'a, K: 'a, V: 'a, const B: usize> Iterator for IterMut<'a, K, V, B> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        let (node, idx) = advance_stack(&mut self.stack, &mut self.stack_len)?;
        self.remaining -= 1;
        // SAFETY: advance_stack returns a valid (node, idx) where idx < node.len.
        // &mut self ensures no other mutable references exist.
        Some(unsafe { (key_at(node, idx), value_at_mut(node, idx)) })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}
impl<'a, K: 'a, V: 'a, const B: usize> ExactSizeIterator for IterMut<'a, K, V, B> {}

/// Mutable values iterator.
pub struct ValuesMut<'a, K, V, const B: usize> {
    inner: IterMut<'a, K, V, B>,
}
impl<'a, K: 'a, V: 'a, const B: usize> Iterator for ValuesMut<'a, K, V, B> {
    type Item = &'a mut V;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}
impl<'a, K: 'a, V: 'a, const B: usize> ExactSizeIterator for ValuesMut<'a, K, V, B> {}

/// Range iterator.
pub struct Range<'a, K, V, const B: usize> {
    stack: [(NodePtr<K, V, B>, u16); MAX_DEPTH],
    stack_len: usize,
    end_node: NodePtr<K, V, B>,
    end_idx: u16,
    _marker: PhantomData<&'a ()>,
}
impl<'a, K: 'a, V: 'a, const B: usize> Iterator for Range<'a, K, V, B> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        let (node, idx) = advance_stack_range(
            &mut self.stack,
            &mut self.stack_len,
            self.end_node,
            self.end_idx,
        )?;
        // SAFETY: advance_stack_range returns a valid (node, idx) where idx < node.len.
        Some(unsafe { (key_at(node, idx), value_at(node, idx)) })
    }
}

/// Mutable range iterator.
pub struct RangeMut<'a, K, V, const B: usize> {
    stack: [(NodePtr<K, V, B>, u16); MAX_DEPTH],
    stack_len: usize,
    end_node: NodePtr<K, V, B>,
    end_idx: u16,
    _marker: PhantomData<&'a mut ()>,
}
impl<'a, K: 'a, V: 'a, const B: usize> Iterator for RangeMut<'a, K, V, B> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        let (node, idx) = advance_stack_range(
            &mut self.stack,
            &mut self.stack_len,
            self.end_node,
            self.end_idx,
        )?;
        // SAFETY: advance_stack_range returns a valid (node, idx) where idx < node.len.
        // &mut self ensures no other mutable references exist.
        Some(unsafe { (key_at(node, idx), value_at_mut(node, idx)) })
    }
}

// =============================================================================
// Entry API
// =============================================================================

/// Entry for B-tree.
pub enum Entry<'a, K, V, const B: usize, C, S: SlabOps<BTreeNode<K, V, B>>> {
    /// Occupied.
    Occupied(OccupiedEntry<'a, K, V, B, C, S>),
    /// Vacant.
    Vacant(VacantEntry<'a, K, V, B, C, S>),
}

/// Occupied entry.
pub struct OccupiedEntry<'a, K, V, const B: usize, C, S: SlabOps<BTreeNode<K, V, B>>> {
    tree: &'a mut BTree<K, V, B, C>,
    slab: &'a S,
    node: NodePtr<K, V, B>,
    idx: usize,
}

/// Vacant entry.
pub struct VacantEntry<'a, K, V, const B: usize, C, S: SlabOps<BTreeNode<K, V, B>>> {
    tree: &'a mut BTree<K, V, B, C>,
    slab: &'a S,
    key: K,
}

impl<K, V, const B: usize, C: Compare<K>, S: SlabOps<BTreeNode<K, V, B>>> Entry<'_, K, V, B, C, S> {
    /// Returns a reference to this entry's key.
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(e) => e.key(),
            Entry::Vacant(e) => e.key(),
        }
    }

    /// Modifies an existing entry.
    pub fn and_modify<F: FnOnce(&mut V)>(mut self, f: F) -> Self {
        if let Entry::Occupied(ref mut e) = self {
            f(e.get_mut());
        }
        self
    }
}

impl<'a, K, V, const B: usize, C: Compare<K>, S: SlabOps<BTreeNode<K, V, B>>>
    OccupiedEntry<'a, K, V, B, C, S>
{
    /// Key reference.
    pub fn key(&self) -> &K {
        // SAFETY: self.node is a valid node and self.idx < node.len.
        unsafe { key_at(self.node, self.idx) }
    }
    /// Value reference.
    pub fn get(&self) -> &V {
        // SAFETY: self.node is a valid node and self.idx < node.len.
        unsafe { value_at(self.node, self.idx) }
    }
    /// Mutable value reference.
    pub fn get_mut(&mut self) -> &mut V {
        // SAFETY: self.node is a valid node; &mut self ensures exclusivity.
        unsafe { value_at_mut(self.node, self.idx) }
    }
    /// Convert to mutable reference.
    pub fn into_mut(self) -> &'a mut V {
        // SAFETY: self.node is a valid node; entry is consumed.
        unsafe { value_at_mut(self.node, self.idx) }
    }
    /// Set value, return old.
    pub fn insert(&mut self, value: V) -> V {
        // SAFETY: self.node is a valid node; self.idx < node.len; values[idx] initialized.
        let slot = unsafe { &mut (*node_deref_mut(self.node)).values[self.idx] };
        // SAFETY: values[self.idx] is initialized (self.idx < node.len by OccupiedEntry invariant).
        let old = unsafe { slot.assume_init_read() };
        *slot = MaybeUninit::new(value);
        old
    }
    /// Remove entry.
    // TODO(perf): Entry removal re-searches from root because the rebalancing
    // algorithm needs the full path. Storing the path in the entry would avoid
    // this O(log n) overhead but costs ~512 bytes of stack.
    pub fn remove(self) -> (K, V) {
        // SAFETY: self.node is a valid node; keys[self.idx] is initialized.
        // ManuallyDrop prevents double-free — remove_entry will properly take it.
        let key_copy = std::mem::ManuallyDrop::new(unsafe {
            (*node_deref(self.node)).keys[self.idx].assume_init_read()
        });
        self.tree
            .remove_entry(self.slab, &key_copy)
            .expect("occupied entry must exist")
    }
}

impl<K, V, const B: usize, C: Compare<K>, S: SlabOps<BTreeNode<K, V, B>>>
    VacantEntry<'_, K, V, B, C, S>
{
    /// Key reference.
    pub fn key(&self) -> &K {
        &self.key
    }
}

impl<'a, K, V, const B: usize, C: Compare<K>>
    VacantEntry<'a, K, V, B, C, bounded::Slab<BTreeNode<K, V, B>>>
{
    /// Try to insert.
    ///
    /// Returns `Err(Full((key, value)))` if the slab is at capacity.
    pub fn try_insert(self, value: V) -> Result<&'a mut V, Full<(K, V)>> {
        let VacantEntry { tree, slab, key } = self;
        let (val_ptr, _) = tree.try_insert_inner(slab, key, value)?;
        // SAFETY: val_ptr points to an initialized value in a valid slab-allocated node.
        Ok(unsafe { &mut *val_ptr })
    }
    /// Insert (panics if full).
    pub fn insert(self, value: V) -> &'a mut V {
        let VacantEntry { tree, slab, key } = self;
        let (val_ptr, _) = tree
            .try_insert_inner(slab, key, value)
            .expect("slab is full");
        // SAFETY: val_ptr points to an initialized value in a valid slab-allocated node.
        unsafe { &mut *val_ptr }
    }
}

impl<'a, K, V, const B: usize, C: Compare<K>>
    VacantEntry<'a, K, V, B, C, nexus_slab::unbounded::Slab<BTreeNode<K, V, B>>>
{
    /// Insert a value into the vacant entry.
    ///
    /// Cannot fail — the unbounded slab grows as needed.
    pub fn insert(self, value: V) -> &'a mut V {
        let VacantEntry { tree, slab, key } = self;
        let (val_ptr, _) = tree.insert_inner(slab, key, value);
        // SAFETY: val_ptr points to an initialized value in a valid slab-allocated node.
        unsafe { &mut *val_ptr }
    }
}

// =============================================================================
// Cursor
// =============================================================================

/// B-tree cursor.
pub struct Cursor<'a, K, V, const B: usize, C, S: SlabOps<BTreeNode<K, V, B>>> {
    tree: &'a mut BTree<K, V, B, C>,
    slab: &'a S,
    stack: [(NodePtr<K, V, B>, u16); MAX_DEPTH],
    stack_len: usize,
    started: bool,
}

impl<K, V, const B: usize, C: Compare<K>, S: SlabOps<BTreeNode<K, V, B>>>
    Cursor<'_, K, V, B, C, S>
{
    /// Key at cursor.
    pub fn key(&self) -> Option<&K> {
        if self.stack_len == 0 || !self.started {
            return None;
        }
        let (node, idx) = self.stack[self.stack_len - 1];
        // SAFETY: node is a valid B-tree node from traversal stack.
        if (idx as usize) >= unsafe { node_len(node) } {
            return None;
        }
        // SAFETY: idx < node.len (checked above); node is a valid traversal-stack node.
        Some(unsafe { key_at(node, idx as usize) })
    }

    /// Value at cursor.
    pub fn value(&self) -> Option<&V> {
        if self.stack_len == 0 || !self.started {
            return None;
        }
        let (node, idx) = self.stack[self.stack_len - 1];
        // SAFETY: node is a valid B-tree node from traversal stack.
        if (idx as usize) >= unsafe { node_len(node) } {
            return None;
        }
        // SAFETY: idx < node.len (checked above); node is a valid traversal-stack node.
        Some(unsafe { value_at(node, idx as usize) })
    }

    /// Mutable value at cursor.
    pub fn value_mut(&mut self) -> Option<&mut V> {
        if self.stack_len == 0 || !self.started {
            return None;
        }
        let (node, idx) = self.stack[self.stack_len - 1];
        // SAFETY: node is a valid B-tree node; &mut self ensures exclusivity.
        if (idx as usize) >= unsafe { node_len(node) } {
            return None;
        }
        // SAFETY: idx < node.len (checked above); node is a valid traversal-stack node; &mut self ensures exclusivity.
        Some(unsafe { value_at_mut(node, idx as usize) })
    }

    /// Advance cursor.
    pub fn advance(&mut self) -> bool {
        if self.started {
            advance_stack(&mut self.stack, &mut self.stack_len);
        } else {
            self.started = true;
            if !self.tree.root.is_null() {
                push_leftmost_path(self.tree.root, &mut self.stack, &mut self.stack_len);
            }
        }
        self.key().is_some()
    }

    /// Remove at cursor.
    pub fn remove(&mut self) -> Option<(K, V)> {
        if self.stack_len == 0 || !self.started {
            return None;
        }
        let (node, idx) = self.stack[self.stack_len - 1];
        let i = idx as usize;
        // SAFETY: node is a valid B-tree node from traversal stack.
        if i >= unsafe { node_len(node) } {
            return None;
        }

        // SAFETY: keys[i] is initialized for i < node.len. ManuallyDrop
        // prevents double-free — remove_entry will properly take the key.
        let key_copy =
            std::mem::ManuallyDrop::new(unsafe { (*node_deref(node)).keys[i].assume_init_read() });
        let result = self.tree.remove_entry(self.slab, &key_copy);

        self.stack_len = 0;
        if let Some((ref removed_key, _)) = result
            && !self.tree.is_empty()
        {
            init_upper_bound_stack::<K, V, B, C>(
                self.tree.root,
                removed_key,
                &mut self.stack,
                &mut self.stack_len,
            );
        }
        result
    }
}

// =============================================================================
// Drain
// =============================================================================

/// Draining iterator.
pub struct DrainBTree<'a, K, V, const B: usize, C, S: SlabOps<BTreeNode<K, V, B>>> {
    tree: &'a mut BTree<K, V, B, C>,
    slab: &'a S,
}

impl<K, V, const B: usize, C: Compare<K>, S: SlabOps<BTreeNode<K, V, B>>> Iterator
    for DrainBTree<'_, K, V, B, C, S>
{
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.tree.pop_first(self.slab)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.tree.len(), Some(self.tree.len()))
    }
}
impl<K, V, const B: usize, C: Compare<K>, S: SlabOps<BTreeNode<K, V, B>>> ExactSizeIterator
    for DrainBTree<'_, K, V, B, C, S>
{
}

impl<K, V, const B: usize, C, S: SlabOps<BTreeNode<K, V, B>>> Drop
    for DrainBTree<'_, K, V, B, C, S>
{
    fn drop(&mut self) {
        self.tree.clear(self.slab);
    }
}
