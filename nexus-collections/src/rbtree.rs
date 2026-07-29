//! Red-black tree sorted map with external slab allocation.
//!
//! # Design
//!
//! A self-balancing BST providing deterministic O(log n) worst case for insert,
//! lookup, and removal. At most 2 rotations per insert, 3 per delete. Slab-allocated
//! nodes via `nexus-slab` for zero allocation after init.
//!
//! # Allocation Model
//!
//! The tree does NOT store the slab. The slab is passed to methods that
//! allocate or free nodes (`insert`, `remove`, `clear`). Read-only methods
//! (`get`, `iter`) do not need the slab.
//!
//! # Example
//!
//! ```ignore
//! use nexus_slab::bounded::Slab;
//! use nexus_collections::rbtree::RbTree;
//!
//! let slab = unsafe { Slab::<RbNode<u64, String>>::with_capacity(1000) };
//! let mut map = RbTree::new();
//! map.try_insert(&slab, 100, "hello".into()).unwrap();
//! assert_eq!(map.get(&100), Some(&"hello".into()));
//! ```

use std::cell::Cell;
use std::cmp::Ordering;
use std::fmt;
use std::marker::PhantomData;
use std::ptr;

use nexus_slab::bounded;
use nexus_slab::shared::{Full, Slot, SlotCell};

use crate::SlabOps;
use crate::compare::{Compare, Natural};

// =============================================================================
// Color constants — packed into the LSB of parent pointer
// =============================================================================

const COLOR_RED: usize = 0;
const COLOR_BLACK: usize = 1;
const COLOR_MASK: usize = 1;
const PARENT_MASK: usize = !1;

// =============================================================================
// NodePtr
// =============================================================================

/// Raw pointer to a slab-allocated RB tree node.
type NodePtr<K, V> = *mut SlotCell<RbNode<K, V>>;

// =============================================================================
// RbNode<K, V>
// =============================================================================

// Verify that node alignment is sufficient for color-in-LSB encoding.
// RbNode uses the LSB of parent pointers for color storage, requiring
// at least 2-byte alignment of the node allocation.
const _: () = assert!(
    core::mem::align_of::<RbNode<(), ()>>() >= 2,
    "RbNode must be at least 2-byte aligned for color-in-LSB encoding"
);

/// A node in a red-black tree sorted map.
///
/// Color is packed into the LSB of the parent pointer (slab nodes are at
/// least 8-byte aligned, guaranteeing the low 3 bits are zero).
#[repr(C)]
pub struct RbNode<K, V> {
    key: K,
    left: Cell<NodePtr<K, V>>,
    right: Cell<NodePtr<K, V>>,
    parent_color: Cell<usize>,
    value: V,
}

impl<K, V> RbNode<K, V> {
    /// Creates a new detached red node with the given key and value.
    pub fn new(key: K, value: V) -> Self {
        RbNode {
            key,
            left: Cell::new(ptr::null_mut()),
            right: Cell::new(ptr::null_mut()),
            parent_color: Cell::new(COLOR_RED),
            value,
        }
    }

    /// Returns a reference to the key.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Returns a reference to the value.
    pub fn value(&self) -> &V {
        &self.value
    }

    /// Returns a mutable reference to the value.
    pub fn value_mut(&mut self) -> &mut V {
        &mut self.value
    }

    /// Consumes the node, returning `(key, value)`.
    #[doc(hidden)]
    pub fn into_value(self) -> (K, V) {
        (self.key, self.value)
    }
}

// =============================================================================
// Packed parent/color helpers
// =============================================================================

fn get_parent<K, V>(ptr: NodePtr<K, V>) -> NodePtr<K, V> {
    // SAFETY: ptr is non-null and points to a valid tree node.
    let packed = unsafe { (*node_deref(ptr)).parent_color.get() };
    ptr::with_exposed_provenance_mut(packed & PARENT_MASK)
}

fn set_parent<K, V>(ptr: NodePtr<K, V>, parent: NodePtr<K, V>) {
    // SAFETY: ptr is non-null and points to a valid tree node.
    let node = unsafe { &*node_deref(ptr) };
    let color = node.parent_color.get() & COLOR_MASK;
    let parent_bits = parent.expose_provenance();
    node.parent_color.set(parent_bits | color);
}

fn set_parent_color<K, V>(ptr: NodePtr<K, V>, parent: NodePtr<K, V>, color: usize) {
    // SAFETY: ptr is non-null and points to a valid tree node.
    let node = unsafe { &*node_deref(ptr) };
    let parent_bits = parent.expose_provenance();
    node.parent_color.set(parent_bits | color);
}

// =============================================================================
// node_deref
// =============================================================================

/// Dereferences a `NodePtr` to get a const pointer to the `RbNode`.
///
/// # Safety
///
/// `ptr` must be non-null and point to an occupied `SlotCell`.
unsafe fn node_deref<K, V>(ptr: NodePtr<K, V>) -> *const RbNode<K, V> {
    // SAFETY: SlotCell::value_ptr() returns the pointer to the stored value.
    unsafe { (*ptr).value_ptr() }
}

/// Dereferences a `NodePtr` to get a mutable pointer to the `RbNode`.
///
/// # Safety
///
/// `ptr` must be non-null and point to an occupied `SlotCell`. The caller
/// must ensure no other references to this node exist.
unsafe fn node_deref_mut<K, V>(ptr: NodePtr<K, V>) -> *mut RbNode<K, V> {
    // Use value_ptr_mut to avoid creating &SlotCell which would give
    // read-only provenance under stacked borrows.
    // SAFETY: ptr is non-null and points to an occupied SlotCell per caller contract.
    unsafe { nexus_slab::shared::SlotCell::value_ptr_mut(ptr) }
}

// =============================================================================
// Color helpers
// =============================================================================

fn is_red<K, V>(ptr: NodePtr<K, V>) -> bool {
    if ptr.is_null() {
        return false;
    }
    // SAFETY: ptr is non-null and points to a valid tree node.
    unsafe { (*node_deref(ptr)).parent_color.get() & COLOR_MASK == COLOR_RED }
}

fn set_color<K, V>(ptr: NodePtr<K, V>, color: usize) {
    if !ptr.is_null() {
        // SAFETY: ptr is non-null and points to a valid tree node.
        let node = unsafe { &*node_deref(ptr) };
        let packed = node.parent_color.get();
        node.parent_color.set((packed & PARENT_MASK) | color);
    }
}

// =============================================================================
// Tree navigation helpers
// =============================================================================

/// # Safety
///
/// `ptr` must be non-null and point to a valid tree node.
unsafe fn tree_minimum<K, V>(mut ptr: NodePtr<K, V>) -> NodePtr<K, V> {
    loop {
        // SAFETY: ptr is a valid tree node per caller / loop invariant.
        let left = unsafe { (*node_deref(ptr)).left.get() };
        if left.is_null() {
            return ptr;
        }
        ptr = left;
    }
}

/// # Safety
///
/// `ptr` must be non-null and point to a valid tree node.
unsafe fn tree_maximum<K, V>(mut ptr: NodePtr<K, V>) -> NodePtr<K, V> {
    loop {
        // SAFETY: ptr is a valid tree node per caller / loop invariant.
        let right = unsafe { (*node_deref(ptr)).right.get() };
        if right.is_null() {
            return ptr;
        }
        ptr = right;
    }
}

/// # Safety
///
/// `ptr` must be non-null and point to a valid tree node.
unsafe fn successor<K, V>(ptr: NodePtr<K, V>) -> NodePtr<K, V> {
    // SAFETY: ptr is a valid tree node per caller contract.
    let node = unsafe { &*node_deref(ptr) };
    let right = node.right.get();
    if !right.is_null() {
        // SAFETY: right is non-null (checked above) and a valid tree node.
        return unsafe { tree_minimum(right) };
    }
    let mut current = ptr;
    let mut parent = get_parent(ptr);
    while !parent.is_null() {
        // SAFETY: parent is non-null and a valid tree node.
        if current != unsafe { (*node_deref(parent)).right.get() } {
            break;
        }
        current = parent;
        parent = get_parent(parent);
    }
    parent
}

/// # Safety
///
/// `ptr` must be non-null and point to a valid tree node.
unsafe fn predecessor<K, V>(ptr: NodePtr<K, V>) -> NodePtr<K, V> {
    // SAFETY: ptr is a valid tree node per caller contract.
    let node = unsafe { &*node_deref(ptr) };
    let left = node.left.get();
    if !left.is_null() {
        // SAFETY: left is non-null (checked above) and a valid tree node.
        return unsafe { tree_maximum(left) };
    }
    let mut current = ptr;
    let mut parent = get_parent(ptr);
    while !parent.is_null() {
        // SAFETY: parent is non-null and a valid tree node.
        if current != unsafe { (*node_deref(parent)).left.get() } {
            break;
        }
        current = parent;
        parent = get_parent(parent);
    }
    parent
}

// =============================================================================
// RbTree<K, V, C>
// =============================================================================

/// A self-balancing sorted map with external slab allocation.
///
/// # Panic Safety
///
/// If a comparator panics during a tree mutation (insert/remove), the tree
/// may be left in an inconsistent state with partially-updated pointers.
/// Subsequent operations on such a tree are undefined behavior. Callers
/// are responsible for ensuring their `Compare` implementation does not panic.
pub struct RbTree<K, V, C = Natural> {
    root: NodePtr<K, V>,
    leftmost: NodePtr<K, V>,
    rightmost: NodePtr<K, V>,
    len: usize,
    _marker: PhantomData<C>,
}

// =============================================================================
// impl — base block (requires Compare)
// =============================================================================

impl<K, V, C: Compare<K>> RbTree<K, V, C> {
    /// Returns `true` if the tree contains the given key.
    pub fn contains_key(&self, key: &K) -> bool {
        self.find(key).is_some()
    }

    /// Returns a reference to the value for the given key.
    pub fn get(&self, key: &K) -> Option<&V> {
        let ptr = self.find(key)?;
        // SAFETY: find() returned a non-null valid tree node.
        Some(unsafe { &(*node_deref(ptr)).value })
    }

    /// Returns a mutable reference to the value for the given key.
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let ptr = self.find(key)?;
        // SAFETY: find() returned a non-null valid tree node; &mut self ensures exclusivity.
        Some(unsafe { &mut (*node_deref_mut(ptr)).value })
    }

    /// Returns references to the key and value for the given key.
    pub fn get_key_value(&self, key: &K) -> Option<(&K, &V)> {
        let ptr = self.find(key)?;
        // SAFETY: find() returned a non-null valid tree node.
        let node = unsafe { &*node_deref(ptr) };
        Some((&node.key, &node.value))
    }

    // =========================================================================
    // Mutation — remove / pop / clear
    // =========================================================================

    /// Removes the node with the given key and returns the value.
    pub fn remove(&mut self, slab: &impl SlabOps<RbNode<K, V>>, key: &K) -> Option<V> {
        let (_, v) = self.remove_entry(slab, key)?;
        Some(v)
    }

    /// Removes the node with the given key and returns `(key, value)`.
    pub fn remove_entry(&mut self, slab: &impl SlabOps<RbNode<K, V>>, key: &K) -> Option<(K, V)> {
        let ptr = self.find(key)?;

        let result = self.remove_node(slab, ptr);

        Some(result)
    }

    /// Removes and returns the first (smallest) key-value pair.
    pub fn pop_first(&mut self, slab: &impl SlabOps<RbNode<K, V>>) -> Option<(K, V)> {
        if self.leftmost.is_null() {
            return None;
        }

        let result = self.remove_node(slab, self.leftmost);

        Some(result)
    }

    /// Removes and returns the last (largest) key-value pair.
    pub fn pop_last(&mut self, slab: &impl SlabOps<RbNode<K, V>>) -> Option<(K, V)> {
        if self.rightmost.is_null() {
            return None;
        }

        let result = self.remove_node(slab, self.rightmost);

        Some(result)
    }

    // =========================================================================
    // Insert — bounded slab
    // =========================================================================

    /// Inserts a key-value pair, or returns the pair if the slab is full.
    ///
    /// Use with a [`bounded::Slab`]. For an infallible insert with an
    /// unbounded slab, see [`insert`](Self::insert).
    pub fn try_insert(
        &mut self,
        slab: &bounded::Slab<RbNode<K, V>>,
        key: K,
        value: V,
    ) -> Result<Option<V>, Full<(K, V)>> {
        let mut parent: NodePtr<K, V> = ptr::null_mut();
        let mut is_left = true;
        let mut current = self.root;

        while !current.is_null() {
            parent = current;
            // SAFETY: current is non-null and a valid tree node.
            let node = unsafe { &*node_deref(current) };
            match C::cmp(&key, &node.key) {
                Ordering::Equal => {
                    // SAFETY: current is a valid node; &mut self ensures exclusivity.
                    let existing = unsafe { &mut (*node_deref_mut(current)).value };
                    return Ok(Some(std::mem::replace(existing, value)));
                }
                Ordering::Less => {
                    is_left = true;
                    current = node.left.get();
                }
                Ordering::Greater => {
                    is_left = false;
                    current = node.right.get();
                }
            }
        }

        match slab.try_alloc(RbNode::new(key, value)) {
            Ok(slot) => {
                let ptr = slot.into_raw();

                self.link_new_node(ptr, parent, is_left);

                Ok(None)
            }
            Err(full) => Err(Full(full.into_inner().into_value())),
        }
    }

    /// Inserts a key-value pair. Cannot fail — the unbounded slab grows as needed.
    pub fn insert(
        &mut self,
        slab: &nexus_slab::unbounded::Slab<RbNode<K, V>>,
        key: K,
        value: V,
    ) -> Option<V> {
        let mut parent: NodePtr<K, V> = ptr::null_mut();
        let mut is_left = true;
        let mut current = self.root;

        while !current.is_null() {
            parent = current;
            // SAFETY: current is non-null and a valid tree node.
            let node = unsafe { &*node_deref(current) };
            match C::cmp(&key, &node.key) {
                Ordering::Equal => {
                    // SAFETY: current is a valid node; &mut self ensures exclusivity.
                    let existing = unsafe { &mut (*node_deref_mut(current)).value };
                    return Some(std::mem::replace(existing, value));
                }
                Ordering::Less => {
                    is_left = true;
                    current = node.left.get();
                }
                Ordering::Greater => {
                    is_left = false;
                    current = node.right.get();
                }
            }
        }

        let slot = slab.alloc(RbNode::new(key, value));
        let ptr = slot.into_raw();

        self.link_new_node(ptr, parent, is_left);

        None
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
    pub fn entry<'a, S: SlabOps<RbNode<K, V>>>(
        &'a mut self,
        slab: &'a S,
        key: K,
    ) -> Entry<'a, K, V, C, S> {
        let mut parent: NodePtr<K, V> = ptr::null_mut();
        let mut is_left = true;
        let mut current = self.root;

        while !current.is_null() {
            parent = current;
            // SAFETY: current is non-null and a valid tree node (root or child).
            let node = unsafe { &*node_deref(current) };
            match C::cmp(&key, &node.key) {
                Ordering::Equal => {
                    drop(key);
                    return Entry::Occupied(OccupiedEntry {
                        tree: self,
                        slab,
                        ptr: current,
                    });
                }
                Ordering::Less => {
                    is_left = true;
                    current = node.left.get();
                }
                Ordering::Greater => {
                    is_left = false;
                    current = node.right.get();
                }
            }
        }

        Entry::Vacant(VacantEntry {
            tree: self,
            slab,
            key,
            parent,
            is_left,
        })
    }

    // =========================================================================
    // Iteration
    // =========================================================================

    /// Returns an iterator over `(&K, &V)` pairs in sorted order.
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            front: self.leftmost,
            len: self.len,
            _marker: PhantomData,
        }
    }

    /// Returns an iterator over keys in sorted order.
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys { inner: self.iter() }
    }

    /// Returns an iterator over values in key-sorted order.
    pub fn values(&self) -> Values<'_, K, V> {
        Values { inner: self.iter() }
    }

    /// Returns a mutable iterator over `(&K, &mut V)` pairs in sorted order.
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            front: self.leftmost,
            len: self.len,
            _marker: PhantomData,
        }
    }

    /// Returns a mutable iterator over values in key-sorted order.
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }

    /// Returns an iterator over `(&K, &V)` pairs within the given range.
    pub fn range<R: std::ops::RangeBounds<K>>(&self, range: R) -> Range<'_, K, V> {
        let (front, end) = self.resolve_range_bounds(range);
        Range {
            front,
            end,
            _marker: PhantomData,
        }
    }

    /// Returns a mutable iterator over `(&K, &mut V)` pairs within the given range.
    pub fn range_mut<R: std::ops::RangeBounds<K>>(&mut self, range: R) -> RangeMut<'_, K, V> {
        let (front, end) = self.resolve_range_bounds(range);
        RangeMut {
            front,
            end,
            _marker: PhantomData,
        }
    }

    // =========================================================================
    // Cursor
    // =========================================================================

    /// Returns a cursor positioned before the first element.
    pub fn cursor_front<'a, S: SlabOps<RbNode<K, V>>>(
        &'a mut self,
        slab: &'a S,
    ) -> Cursor<'a, K, V, C, S> {
        Cursor {
            tree: self,
            slab,
            current: ptr::null_mut(),
            started: false,
        }
    }

    /// Returns a cursor positioned at the given key.
    pub fn cursor_at<'a, S: SlabOps<RbNode<K, V>>>(
        &'a mut self,
        slab: &'a S,
        key: &K,
    ) -> Cursor<'a, K, V, C, S> {
        let current = self.find(key).unwrap_or_else(|| self.lower_bound(key));
        Cursor {
            tree: self,
            slab,
            current,
            started: true,
        }
    }

    // =========================================================================
    // Drain
    // =========================================================================

    /// Returns a draining iterator.
    pub fn drain<'a, S: SlabOps<RbNode<K, V>>>(&'a mut self, slab: &'a S) -> Drain<'a, K, V, C, S> {
        Drain { tree: self, slab }
    }

    // =========================================================================
    // Internal algorithms
    // =========================================================================

    fn find(&self, key: &K) -> Option<NodePtr<K, V>> {
        let mut current = self.root;
        while !current.is_null() {
            // SAFETY: current is non-null and a valid tree node (root or child).
            let node = unsafe { &*node_deref(current) };
            match C::cmp(key, &node.key) {
                Ordering::Equal => return Some(current),
                Ordering::Less => current = node.left.get(),
                Ordering::Greater => current = node.right.get(),
            }
        }
        None
    }

    fn lower_bound(&self, key: &K) -> NodePtr<K, V> {
        let mut result: NodePtr<K, V> = ptr::null_mut();
        let mut current = self.root;
        while !current.is_null() {
            // SAFETY: current is non-null and a valid tree node (root or child).
            let node = unsafe { &*node_deref(current) };
            if C::cmp(key, &node.key) == Ordering::Greater {
                current = node.right.get();
            } else {
                result = current;
                current = node.left.get();
            }
        }
        result
    }

    fn upper_bound(&self, key: &K) -> NodePtr<K, V> {
        let mut result: NodePtr<K, V> = ptr::null_mut();
        let mut current = self.root;
        while !current.is_null() {
            // SAFETY: current is non-null and a valid tree node (root or child).
            let node = unsafe { &*node_deref(current) };
            if C::cmp(key, &node.key) == Ordering::Less {
                result = current;
                current = node.left.get();
            } else {
                current = node.right.get();
            }
        }
        result
    }

    fn resolve_range_bounds<R: std::ops::RangeBounds<K>>(
        &self,
        range: R,
    ) -> (NodePtr<K, V>, NodePtr<K, V>) {
        use std::ops::Bound;

        let front = match range.start_bound() {
            Bound::Unbounded => self.leftmost,
            Bound::Included(k) => self.lower_bound(k),
            Bound::Excluded(k) => self.upper_bound(k),
        };

        let end = match range.end_bound() {
            Bound::Unbounded => ptr::null_mut(),
            Bound::Included(k) => self.upper_bound(k),
            Bound::Excluded(k) => self.lower_bound(k),
        };

        if front.is_null() || front == end {
            return (ptr::null_mut(), ptr::null_mut());
        }

        if !end.is_null() {
            // SAFETY: front and end are non-null valid tree nodes from lower/upper_bound.
            let front_key = unsafe { &(*node_deref(front)).key };
            // SAFETY: same as above; end is non-null and a valid tree node from lower/upper_bound.
            let end_key = unsafe { &(*node_deref(end)).key };
            if C::cmp(front_key, end_key) != Ordering::Less {
                return (ptr::null_mut(), ptr::null_mut());
            }
        }

        (front, end)
    }

    fn link_new_node(&mut self, ptr: NodePtr<K, V>, parent: NodePtr<K, V>, is_left: bool) {
        set_parent_color(ptr, parent, COLOR_RED);

        if parent.is_null() {
            self.root = ptr;
            self.leftmost = ptr;
            self.rightmost = ptr;
        } else if is_left {
            // SAFETY: parent is non-null and a valid tree node.
            unsafe { (*node_deref(parent)).left.set(ptr) };
            if parent == self.leftmost {
                self.leftmost = ptr;
            }
        } else {
            // SAFETY: parent is non-null and a valid tree node.
            unsafe { (*node_deref(parent)).right.set(ptr) };
            if parent == self.rightmost {
                self.rightmost = ptr;
            }
        }

        self.len += 1;
        // SAFETY: ptr is a valid newly linked red node.
        unsafe { self.insert_fixup(ptr) };
    }

    fn remove_node(&mut self, slab: &impl SlabOps<RbNode<K, V>>, ptr: NodePtr<K, V>) -> (K, V) {
        let new_leftmost = if ptr == self.leftmost {
            if self.len == 1 {
                ptr::null_mut()
            } else {
                // SAFETY: ptr is a valid tree node and not the only one.
                unsafe { successor(ptr) }
            }
        } else {
            self.leftmost
        };
        let new_rightmost = if ptr == self.rightmost {
            if self.len == 1 {
                ptr::null_mut()
            } else {
                // SAFETY: ptr is a valid tree node and not the only one.
                unsafe { predecessor(ptr) }
            }
        } else {
            self.rightmost
        };

        // SAFETY: ptr is a valid tree node to be deleted.
        unsafe { self.delete_node(ptr) };
        self.len -= 1;
        self.leftmost = new_leftmost;
        self.rightmost = new_rightmost;

        // SAFETY: ptr was obtained from Slot::into_raw() during insert.
        // After delete_node, it is unwired from the tree and safe to reclaim.
        let slot = unsafe { Slot::from_raw(ptr) };
        let node = slab.take_slot(slot);
        node.into_value()
    }

    // =========================================================================
    // Rotations
    // =========================================================================

    /// Left rotation around `x`. `x` and `x.right` must be non-null valid nodes.
    unsafe fn rotate_left(&mut self, x: NodePtr<K, V>) {
        // SAFETY: x is a valid non-null tree node. y = x.right is guaranteed
        // non-null by the RB-tree fixup algorithm that calls this.
        let x_node = unsafe { &*node_deref(x) };
        let y = x_node.right.get();
        // SAFETY: y is non-null per the caller-guaranteed invariant above; it is a valid tree node.
        let y_node = unsafe { &*node_deref(y) };

        let b = y_node.left.get();
        x_node.right.set(b);
        if !b.is_null() {
            set_parent(b, x);
        }

        let p = get_parent(x);
        set_parent(y, p);
        if p.is_null() {
            self.root = y;
        } else {
            // SAFETY: p is non-null and a valid parent node.
            let p_node = unsafe { &*node_deref(p) };
            if x == p_node.left.get() {
                p_node.left.set(y);
            } else {
                p_node.right.set(y);
            }
        }

        y_node.left.set(x);
        set_parent(x, y);
    }

    /// Right rotation around `x`. `x` and `x.left` must be non-null valid nodes.
    unsafe fn rotate_right(&mut self, x: NodePtr<K, V>) {
        // SAFETY: x is a valid non-null tree node. y = x.left is guaranteed
        // non-null by the RB-tree fixup algorithm that calls this.
        let x_node = unsafe { &*node_deref(x) };
        let y = x_node.left.get();
        // SAFETY: y is non-null per the caller-guaranteed invariant above; it is a valid tree node.
        let y_node = unsafe { &*node_deref(y) };

        let b = y_node.right.get();
        x_node.left.set(b);
        if !b.is_null() {
            set_parent(b, x);
        }

        let p = get_parent(x);
        set_parent(y, p);
        if p.is_null() {
            self.root = y;
        } else {
            // SAFETY: p is non-null and a valid parent node.
            let p_node = unsafe { &*node_deref(p) };
            if x == p_node.left.get() {
                p_node.left.set(y);
            } else {
                p_node.right.set(y);
            }
        }

        y_node.right.set(x);
        set_parent(x, y);
    }

    /// Replaces subtree rooted at `u` with subtree rooted at `v`.
    /// `u` must be non-null. `v` may be null.
    unsafe fn transplant(&mut self, u: NodePtr<K, V>, v: NodePtr<K, V>) {
        let u_parent = get_parent(u);
        if u_parent.is_null() {
            self.root = v;
        } else {
            // SAFETY: u_parent is non-null and a valid tree node.
            let p_node = unsafe { &*node_deref(u_parent) };
            if u == p_node.left.get() {
                p_node.left.set(v);
            } else {
                p_node.right.set(v);
            }
        }
        if !v.is_null() {
            set_parent(v, u_parent);
        }
    }

    // =========================================================================
    // Insert fixup
    // =========================================================================

    /// Standard RB-tree insert fixup. Restores red-black properties after
    /// inserting a red node `z`.
    ///
    /// # Safety
    ///
    /// All node_deref calls below are safe because z, parent, grandparent,
    /// and uncle are all valid tree nodes obtained by traversing parent
    /// pointers from z. The RB-tree structure invariants guarantee these
    /// nodes exist when their pointers are non-null.
    unsafe fn insert_fixup(&mut self, mut z: NodePtr<K, V>) {
        while is_red(get_parent(z)) {
            let parent = get_parent(z);
            let grandparent = get_parent(parent);

            // SAFETY: grandparent is non-null (parent is red, so not root).
            if parent == unsafe { (*node_deref(grandparent)).left.get() } {
                // SAFETY: same as above; grandparent is non-null and a valid tree node.
                let uncle = unsafe { (*node_deref(grandparent)).right.get() };
                if is_red(uncle) {
                    set_color(parent, COLOR_BLACK);
                    set_color(uncle, COLOR_BLACK);
                    set_color(grandparent, COLOR_RED);
                    z = grandparent;
                } else {
                    // SAFETY: parent is non-null and valid.
                    if z == unsafe { (*node_deref(parent)).right.get() } {
                        z = parent;
                        // SAFETY: z was just set to parent which is non-null and a valid tree node.
                        unsafe { self.rotate_left(z) };
                    }
                    let parent = get_parent(z);
                    let grandparent = get_parent(parent);
                    set_color(parent, COLOR_BLACK);
                    set_color(grandparent, COLOR_RED);
                    // SAFETY: grandparent is non-null (parent is red, not root) and a valid tree node.
                    unsafe { self.rotate_right(grandparent) };
                }
            } else {
                // SAFETY: grandparent is non-null (parent is red, not root) and a valid tree node.
                let uncle = unsafe { (*node_deref(grandparent)).left.get() };
                if is_red(uncle) {
                    set_color(parent, COLOR_BLACK);
                    set_color(uncle, COLOR_BLACK);
                    set_color(grandparent, COLOR_RED);
                    z = grandparent;
                } else {
                    // SAFETY: parent is non-null and valid.
                    if z == unsafe { (*node_deref(parent)).left.get() } {
                        z = parent;
                        // SAFETY: z was just set to parent which is non-null and a valid tree node.
                        unsafe { self.rotate_right(z) };
                    }
                    let parent = get_parent(z);
                    let grandparent = get_parent(parent);
                    set_color(parent, COLOR_BLACK);
                    set_color(grandparent, COLOR_RED);
                    // SAFETY: grandparent is non-null (parent is red, not root) and a valid tree node.
                    unsafe { self.rotate_left(grandparent) };
                }
            }
        }
        set_color(self.root, COLOR_BLACK);
    }

    // =========================================================================
    // Delete
    // =========================================================================

    /// Standard RB-tree deletion of node `z`.
    ///
    /// # Safety
    ///
    /// `z` must be a valid non-null node in this tree. All node_deref calls
    /// operate on valid tree nodes reached by following child/parent pointers.
    unsafe fn delete_node(&mut self, z: NodePtr<K, V>) {
        // SAFETY: z is a valid tree node per caller contract.
        let z_node = unsafe { &*node_deref(z) };
        let z_left = z_node.left.get();
        let z_right = z_node.right.get();
        let z_color = z_node.parent_color.get() & COLOR_MASK;

        let y_original_color: usize;
        let x: NodePtr<K, V>;
        let x_parent: NodePtr<K, V>;

        if z_left.is_null() {
            y_original_color = z_color;
            x = z_right;
            x_parent = get_parent(z);
            // SAFETY: z is a valid non-null tree node; transplant accepts null for v.
            unsafe { self.transplant(z, z_right) };
        } else if z_right.is_null() {
            y_original_color = z_color;
            x = z_left;
            x_parent = get_parent(z);
            // SAFETY: z is a valid non-null tree node; z_left is non-null (else branch).
            unsafe { self.transplant(z, z_left) };
        } else {
            // SAFETY: z_right is non-null (both children present in this branch).
            let y = unsafe { tree_minimum(z_right) };
            // SAFETY: y is non-null — tree_minimum returns a valid node from a non-null input.
            let y_node = unsafe { &*node_deref(y) };
            y_original_color = y_node.parent_color.get() & COLOR_MASK;
            x = y_node.right.get();

            if get_parent(y) == z {
                x_parent = y;
            } else {
                x_parent = get_parent(y);
                // SAFETY: y is a valid non-null node (in-order successor); transplant accepts null for v.
                unsafe { self.transplant(y, x) };
                // SAFETY: y is non-null and a valid tree node; setting right via Cell is safe.
                unsafe { (*node_deref(y)).right.set(z_right) };
                set_parent(z_right, y);
            }

            // SAFETY: z and y are both valid non-null tree nodes.
            unsafe { self.transplant(z, y) };
            // SAFETY: y is non-null and a valid tree node; setting left via Cell is safe.
            unsafe { (*node_deref(y)).left.set(z_left) };
            set_parent(z_left, y);
            set_color(y, z_color);
        }

        if y_original_color == COLOR_BLACK {
            // SAFETY: x_parent is a valid node; x may be null (treated as nil leaf).
            unsafe { self.delete_fixup(x, x_parent) };
        }
    }

    /// Standard RB-tree delete fixup. Restores properties after removing a
    /// black node. `x` may be null (representing a nil leaf).
    ///
    /// # Safety
    ///
    /// All node_deref calls operate on valid tree nodes. `x_parent` is always
    /// non-null when the loop runs (x != root implies x has a parent).
    /// Sibling `w` is guaranteed non-null by RB-tree invariants (black-height
    /// balance means a black node's sibling cannot be nil).
    unsafe fn delete_fixup(&mut self, mut x: NodePtr<K, V>, mut x_parent: NodePtr<K, V>) {
        while x != self.root && !is_red(x) {
            // SAFETY: x_parent is non-null (x is not the root).
            if x == unsafe { (*node_deref(x_parent)).left.get() } {
                // SAFETY: same as above; x_parent is non-null and a valid tree node.
                let mut w = unsafe { (*node_deref(x_parent)).right.get() };
                if is_red(w) {
                    set_color(w, COLOR_BLACK);
                    set_color(x_parent, COLOR_RED);
                    // SAFETY: x_parent is non-null and a valid tree node; w is red so rotation valid.
                    unsafe { self.rotate_left(x_parent) };
                    // SAFETY: x_parent is still a valid non-null tree node after the rotation.
                    w = unsafe { (*node_deref(x_parent)).right.get() };
                }
                // SAFETY: w is non-null — RB-tree black-height invariant guarantees a non-nil sibling.
                let w_left = unsafe { (*node_deref(w)).left.get() };
                // SAFETY: same as above; w is a valid non-null sibling node.
                let w_right = unsafe { (*node_deref(w)).right.get() };
                if !is_red(w_left) && !is_red(w_right) {
                    set_color(w, COLOR_RED);
                    x = x_parent;
                    x_parent = get_parent(x);
                } else {
                    if !is_red(w_right) {
                        set_color(w_left, COLOR_BLACK);
                        set_color(w, COLOR_RED);
                        // SAFETY: w is non-null and a valid tree node.
                        unsafe { self.rotate_right(w) };
                        // SAFETY: x_parent is still a valid non-null tree node after the rotation.
                        w = unsafe { (*node_deref(x_parent)).right.get() };
                    }
                    // SAFETY: x_parent is non-null and a valid tree node.
                    let parent_color =
                        unsafe { (*node_deref(x_parent)).parent_color.get() } & COLOR_MASK;
                    set_color(w, parent_color);
                    set_color(x_parent, COLOR_BLACK);
                    // SAFETY: w is non-null and valid; its right child is non-null (w_right is red).
                    set_color(unsafe { (*node_deref(w)).right.get() }, COLOR_BLACK);
                    // SAFETY: x_parent is non-null and a valid tree node.
                    unsafe { self.rotate_left(x_parent) };
                    x = self.root;
                }
            } else {
                // SAFETY: x_parent is non-null and a valid tree node.
                let mut w = unsafe { (*node_deref(x_parent)).left.get() };
                if is_red(w) {
                    set_color(w, COLOR_BLACK);
                    set_color(x_parent, COLOR_RED);
                    // SAFETY: x_parent is non-null and a valid tree node; w is red so rotation valid.
                    unsafe { self.rotate_right(x_parent) };
                    // SAFETY: x_parent is still a valid non-null tree node after the rotation.
                    w = unsafe { (*node_deref(x_parent)).left.get() };
                }
                // SAFETY: w is non-null — RB-tree black-height invariant guarantees a non-nil sibling.
                let w_left = unsafe { (*node_deref(w)).left.get() };
                // SAFETY: same as above; w is a valid non-null sibling node.
                let w_right = unsafe { (*node_deref(w)).right.get() };
                if !is_red(w_right) && !is_red(w_left) {
                    set_color(w, COLOR_RED);
                    x = x_parent;
                    x_parent = get_parent(x);
                } else {
                    if !is_red(w_left) {
                        set_color(w_right, COLOR_BLACK);
                        set_color(w, COLOR_RED);
                        // SAFETY: w is non-null and a valid tree node.
                        unsafe { self.rotate_left(w) };
                        // SAFETY: x_parent is still a valid non-null tree node after the rotation.
                        w = unsafe { (*node_deref(x_parent)).left.get() };
                    }
                    // SAFETY: x_parent is non-null and a valid tree node.
                    let parent_color =
                        unsafe { (*node_deref(x_parent)).parent_color.get() } & COLOR_MASK;
                    set_color(w, parent_color);
                    set_color(x_parent, COLOR_BLACK);
                    // SAFETY: w is non-null and valid; its left child is non-null (w_left is red).
                    set_color(unsafe { (*node_deref(w)).left.get() }, COLOR_BLACK);
                    // SAFETY: x_parent is non-null and a valid tree node.
                    unsafe { self.rotate_right(x_parent) };
                    x = self.root;
                }
            }
        }
        set_color(x, COLOR_BLACK);
    }

    // =========================================================================
    // Invariant verification
    // =========================================================================

    /// Verifies all red-black tree invariants. Panics on violation.
    #[doc(hidden)]
    pub fn verify_invariants(&self) {
        if self.root.is_null() {
            assert!(self.leftmost.is_null() && self.rightmost.is_null());
            assert_eq!(self.len, 0);
            return;
        }
        assert!(!is_red(self.root), "root must be black");
        assert!(
            get_parent(self.root).is_null(),
            "root's parent must be null"
        );

        let mut black_height: Option<usize> = None;
        let mut count = 0usize;
        Self::verify_subtree(self.root, &mut black_height, 0, &mut count);

        // SAFETY: root is non-null (checked above) and a valid tree node.
        let actual_min = unsafe { tree_minimum(self.root) };
        // SAFETY: root is non-null (checked above) and a valid tree node.
        let actual_max = unsafe { tree_maximum(self.root) };
        assert_eq!(self.leftmost, actual_min, "leftmost cache mismatch");
        assert_eq!(self.rightmost, actual_max, "rightmost cache mismatch");
        assert_eq!(
            count, self.len,
            "node count ({count}) != len ({})",
            self.len
        );
    }

    fn verify_subtree(
        ptr: NodePtr<K, V>,
        expected_bh: &mut Option<usize>,
        current_bh: usize,
        count: &mut usize,
    ) {
        if ptr.is_null() {
            let bh = current_bh + 1;
            match *expected_bh {
                None => *expected_bh = Some(bh),
                Some(expected) => assert_eq!(bh, expected, "black-height mismatch"),
            }
            return;
        }

        *count += 1;
        // SAFETY: ptr is non-null (checked above) and a valid tree node
        // reached by recursive traversal from the root.
        let node = unsafe { &*node_deref(ptr) };

        if is_red(ptr) {
            assert!(!is_red(node.left.get()), "red node has red left child");
            assert!(!is_red(node.right.get()), "red node has red right child");
        }

        let left = node.left.get();
        let right = node.right.get();

        if !left.is_null() {
            // SAFETY: left is non-null and a valid child of the current node.
            let left_key = unsafe { &(*node_deref(left)).key };
            assert!(C::cmp(left_key, &node.key) == Ordering::Less);
            assert_eq!(get_parent(left), ptr);
        }
        if !right.is_null() {
            // SAFETY: right is non-null and a valid child of the current node.
            let right_key = unsafe { &(*node_deref(right)).key };
            assert!(C::cmp(right_key, &node.key) == Ordering::Greater);
            assert_eq!(get_parent(right), ptr);
        }

        let next_bh = current_bh + usize::from(!is_red(ptr));
        Self::verify_subtree(left, expected_bh, next_bh, count);
        Self::verify_subtree(right, expected_bh, next_bh, count);
    }
}

// =============================================================================
// new — Natural-specific
// =============================================================================

impl<K, V> RbTree<K, V> {
    /// Creates a new empty red-black tree with natural (`Ord`) key ordering.
    pub fn new() -> Self {
        RbTree {
            root: ptr::null_mut(),
            leftmost: ptr::null_mut(),
            rightmost: ptr::null_mut(),
            len: 0,

            _marker: PhantomData,
        }
    }
}

impl<K, V> Default for RbTree<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

// RbTree does NOT implement Drop in release. The user must call clear() with
// the slab to release nodes. In debug builds, we panic to catch slot leaks.
#[cfg(debug_assertions)]
impl<K, V, C> Drop for RbTree<K, V, C> {
    #[allow(clippy::manual_assert)]
    fn drop(&mut self) {
        if self.len > 0 && !std::thread::panicking() {
            panic!(
                "RbTree dropped with {} elements without calling clear(). \
                 This leaks slab slots. Call tree.clear(&slab) before dropping.",
                self.len
            );
        }
    }
}

// =============================================================================
// Unconstrained methods — no Compare bound
// =============================================================================

impl<K, V, C> RbTree<K, V, C> {
    /// Creates a new empty red-black tree with a custom comparator.
    #[allow(unused_variables, clippy::needless_pass_by_value)]
    pub fn with_comparator(comparator: C) -> Self {
        RbTree {
            root: ptr::null_mut(),
            leftmost: ptr::null_mut(),
            rightmost: ptr::null_mut(),
            len: 0,

            _marker: PhantomData,
        }
    }

    /// Returns the number of elements in the tree.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the tree is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the first (smallest) key-value pair.
    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        if self.leftmost.is_null() {
            return None;
        }
        // SAFETY: leftmost is non-null and a valid tree node.
        let node = unsafe { &*node_deref(self.leftmost) };
        Some((&node.key, &node.value))
    }

    /// Returns the last (largest) key-value pair.
    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        if self.rightmost.is_null() {
            return None;
        }
        // SAFETY: rightmost is non-null and a valid tree node.
        let node = unsafe { &*node_deref(self.rightmost) };
        Some((&node.key, &node.value))
    }

    /// Removes all nodes, freeing them via the slab.
    pub fn clear(&mut self, slab: &impl SlabOps<RbNode<K, V>>) {
        let mut current = self.root;
        while !current.is_null() {
            // SAFETY: current is a valid tree node — either root or reached
            // by following left/right/parent pointers from a valid node.
            let node = unsafe { &*node_deref(current) };
            let left = node.left.get();
            let right = node.right.get();

            if !left.is_null() {
                node.left.set(ptr::null_mut());
                current = left;
            } else if !right.is_null() {
                node.right.set(ptr::null_mut());
                current = right;
            } else {
                let parent = get_parent(current);
                // SAFETY: current was obtained from Slot::into_raw() during insert.
                // It is a leaf with no children, safe to reclaim.
                let slot = unsafe { Slot::from_raw(current) };
                slab.free_slot(slot);
                current = parent;
            }
        }

        self.root = ptr::null_mut();
        self.leftmost = ptr::null_mut();
        self.rightmost = ptr::null_mut();
        self.len = 0;
    }
}

// Note: RbTree does NOT implement Drop. The user must call clear() with the
// slab to free all nodes. This is deliberate.

impl<K: fmt::Debug, V: fmt::Debug, C: Compare<K>> fmt::Debug for RbTree<K, V, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

// =============================================================================
// Entry API
// =============================================================================

/// A view into a single entry in the tree.
pub enum Entry<'a, K, V, C, S: SlabOps<RbNode<K, V>>> {
    /// An occupied entry — key exists in the tree.
    Occupied(OccupiedEntry<'a, K, V, C, S>),
    /// A vacant entry — key does not exist.
    Vacant(VacantEntry<'a, K, V, C, S>),
}

/// A view into an occupied entry in the tree.
pub struct OccupiedEntry<'a, K, V, C, S: SlabOps<RbNode<K, V>>> {
    tree: &'a mut RbTree<K, V, C>,
    slab: &'a S,
    ptr: NodePtr<K, V>,
}

/// A view into a vacant entry in the tree.
pub struct VacantEntry<'a, K, V, C, S: SlabOps<RbNode<K, V>>> {
    tree: &'a mut RbTree<K, V, C>,
    slab: &'a S,
    key: K,
    parent: NodePtr<K, V>,
    is_left: bool,
}

impl<K, V, C: Compare<K>, S: SlabOps<RbNode<K, V>>> Entry<'_, K, V, C, S> {
    /// Returns a reference to this entry's key.
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(e) => e.key(),
            Entry::Vacant(e) => e.key(),
        }
    }

    /// Modifies an existing entry before potential insertion.
    pub fn and_modify<F: FnOnce(&mut V)>(mut self, f: F) -> Self {
        if let Entry::Occupied(ref mut e) = self {
            f(e.get_mut());
        }
        self
    }
}

impl<'a, K, V, C: Compare<K>, S: SlabOps<RbNode<K, V>>> OccupiedEntry<'a, K, V, C, S> {
    /// Returns a reference to the key.
    pub fn key(&self) -> &K {
        // SAFETY: self.ptr is a valid occupied tree node from find().
        unsafe { &(*node_deref(self.ptr)).key }
    }

    /// Returns a reference to the value.
    pub fn get(&self) -> &V {
        // SAFETY: self.ptr is a valid occupied tree node.
        unsafe { &(*node_deref(self.ptr)).value }
    }

    /// Returns a mutable reference to the value.
    pub fn get_mut(&mut self) -> &mut V {
        // SAFETY: self.ptr is a valid tree node; &mut self ensures exclusivity.
        unsafe { &mut (*node_deref_mut(self.ptr)).value }
    }

    /// Converts to a mutable reference with the entry's lifetime.
    pub fn into_mut(self) -> &'a mut V {
        // SAFETY: self.ptr is a valid tree node; entry is consumed.
        unsafe { &mut (*node_deref_mut(self.ptr)).value }
    }

    /// Sets the value and returns the old value.
    pub fn insert(&mut self, value: V) -> V {
        // SAFETY: self.ptr is a valid tree node; &mut self ensures exclusivity.
        let node = unsafe { &mut *node_deref_mut(self.ptr) };
        std::mem::replace(&mut node.value, value)
    }

    /// Removes the entry and returns `(key, value)`.
    pub fn remove(self) -> (K, V) {
        self.tree.remove_node(self.slab, self.ptr)
    }
}

impl<K, V, C: Compare<K>, S: SlabOps<RbNode<K, V>>> VacantEntry<'_, K, V, C, S> {
    /// Returns a reference to the key.
    pub fn key(&self) -> &K {
        &self.key
    }
}

impl<'a, K, V, C: Compare<K>> VacantEntry<'a, K, V, C, bounded::Slab<RbNode<K, V>>> {
    /// Inserts a value into the vacant entry.
    ///
    /// Returns `Err(Full((key, value)))` if the slab is at capacity.
    pub fn try_insert(self, value: V) -> Result<&'a mut V, Full<(K, V)>> {
        let VacantEntry {
            tree,
            slab,
            key,
            parent,
            is_left,
        } = self;
        match slab.try_alloc(RbNode::new(key, value)) {
            Ok(slot) => {
                let ptr = slot.into_raw();
                tree.link_new_node(ptr, parent, is_left);
                // SAFETY: ptr is a freshly allocated and linked valid tree node.
                Ok(unsafe { &mut (*node_deref_mut(ptr)).value })
            }
            Err(full) => Err(Full(full.into_inner().into_value())),
        }
    }

    /// Inserts a value (panics if slab is full).
    pub fn insert(self, value: V) -> &'a mut V {
        let VacantEntry {
            tree,
            slab,
            key,
            parent,
            is_left,
        } = self;
        let slot = slab.alloc(RbNode::new(key, value));
        let ptr = slot.into_raw();
        tree.link_new_node(ptr, parent, is_left);
        // SAFETY: ptr is a freshly allocated and linked valid tree node.
        unsafe { &mut (*node_deref_mut(ptr)).value }
    }
}

impl<'a, K, V, C: Compare<K>> VacantEntry<'a, K, V, C, nexus_slab::unbounded::Slab<RbNode<K, V>>> {
    /// Inserts a value into the vacant entry.
    ///
    /// Cannot fail — the unbounded slab grows as needed.
    pub fn insert(self, value: V) -> &'a mut V {
        let VacantEntry {
            tree,
            slab,
            key,
            parent,
            is_left,
        } = self;
        let slot = slab.alloc(RbNode::new(key, value));
        let ptr = slot.into_raw();
        tree.link_new_node(ptr, parent, is_left);
        // SAFETY: ptr is a freshly allocated and linked valid tree node.
        unsafe { &mut (*node_deref_mut(ptr)).value }
    }
}

// =============================================================================
// Iterators
// =============================================================================

/// Iterator over `(&K, &V)` pairs in sorted order.
pub struct Iter<'a, K, V> {
    front: NodePtr<K, V>,
    len: usize,
    _marker: PhantomData<&'a ()>,
}

impl<'a, K: 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }
        let ptr = self.front;
        // SAFETY: ptr is non-null (len > 0) and a valid tree node from traversal.
        let node = unsafe { &*node_deref(ptr) };
        // SAFETY: ptr is non-null and a valid tree node; successor follows right-subtree/parent pointers within the live tree.
        self.front = unsafe { successor(ptr) };
        self.len -= 1;
        Some((&node.key, &node.value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for Iter<'a, K, V> {}

impl<'a, K: 'a, V, C: Compare<K>> IntoIterator for &'a RbTree<K, V, C> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K: 'a, V, C: Compare<K>> IntoIterator for &'a mut RbTree<K, V, C> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// Iterator over keys in sorted order.
pub struct Keys<'a, K, V> {
    inner: Iter<'a, K, V>,
}

impl<'a, K: 'a, V: 'a> Iterator for Keys<'a, K, V> {
    type Item = &'a K;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}
impl<'a, K: 'a, V: 'a> ExactSizeIterator for Keys<'a, K, V> {}

/// Iterator over values in key-sorted order.
pub struct Values<'a, K, V> {
    inner: Iter<'a, K, V>,
}

impl<'a, K: 'a, V: 'a> Iterator for Values<'a, K, V> {
    type Item = &'a V;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}
impl<'a, K: 'a, V: 'a> ExactSizeIterator for Values<'a, K, V> {}

/// Mutable iterator over `(&K, &mut V)` pairs in sorted order.
pub struct IterMut<'a, K, V> {
    front: NodePtr<K, V>,
    len: usize,
    _marker: PhantomData<&'a mut ()>,
}

impl<'a, K: 'a, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }
        let ptr = self.front;
        // SAFETY: ptr is non-null (len > 0) and a valid tree node.
        let next = unsafe { successor(ptr) };
        // SAFETY: ptr is a valid tree node; &mut self ensures exclusivity.
        let node = unsafe { &mut *node_deref_mut(ptr) };
        self.front = next;
        self.len -= 1;
        Some((&node.key, &mut node.value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}
impl<'a, K: 'a, V: 'a> ExactSizeIterator for IterMut<'a, K, V> {}

/// Mutable iterator over values in key-sorted order.
pub struct ValuesMut<'a, K, V> {
    inner: IterMut<'a, K, V>,
}

impl<'a, K: 'a, V: 'a> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}
impl<'a, K: 'a, V: 'a> ExactSizeIterator for ValuesMut<'a, K, V> {}

/// Iterator over `(&K, &V)` pairs within a key range.
pub struct Range<'a, K, V> {
    front: NodePtr<K, V>,
    end: NodePtr<K, V>,
    _marker: PhantomData<&'a ()>,
}

impl<'a, K: 'a, V: 'a> Iterator for Range<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        if self.front.is_null() || self.front == self.end {
            return None;
        }
        let ptr = self.front;
        // SAFETY: ptr is non-null and a valid tree node within the range.
        let node = unsafe { &*node_deref(ptr) };
        // SAFETY: ptr is non-null and a valid tree node; successor follows right-subtree/parent pointers within the live tree.
        self.front = unsafe { successor(ptr) };
        Some((&node.key, &node.value))
    }
}

/// Mutable iterator over `(&K, &mut V)` pairs within a key range.
pub struct RangeMut<'a, K, V> {
    front: NodePtr<K, V>,
    end: NodePtr<K, V>,
    _marker: PhantomData<&'a mut ()>,
}

impl<'a, K: 'a, V: 'a> Iterator for RangeMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        if self.front.is_null() || self.front == self.end {
            return None;
        }
        let ptr = self.front;
        // SAFETY: ptr is non-null and a valid tree node within the range.
        let next = unsafe { successor(ptr) };
        // SAFETY: ptr is non-null and a valid tree node; &mut self ensures exclusivity over the value.
        let node = unsafe { &mut *node_deref_mut(ptr) };
        self.front = next;
        Some((&node.key, &mut node.value))
    }
}

// =============================================================================
// Cursor
// =============================================================================

/// Cursor for positional traversal with removal.
pub struct Cursor<'a, K, V, C, S: SlabOps<RbNode<K, V>>> {
    tree: &'a mut RbTree<K, V, C>,
    slab: &'a S,
    current: NodePtr<K, V>,
    started: bool,
}

impl<K, V, C: Compare<K>, S: SlabOps<RbNode<K, V>>> Cursor<'_, K, V, C, S> {
    /// Returns a reference to the current key.
    pub fn key(&self) -> Option<&K> {
        if self.current.is_null() {
            return None;
        }
        // SAFETY: current is non-null and a valid tree node from traversal.
        Some(unsafe { &(*node_deref(self.current)).key })
    }

    /// Returns a reference to the current value.
    pub fn value(&self) -> Option<&V> {
        if self.current.is_null() {
            return None;
        }
        // SAFETY: current is non-null and a valid tree node.
        Some(unsafe { &(*node_deref(self.current)).value })
    }

    /// Returns a mutable reference to the current value.
    pub fn value_mut(&mut self) -> Option<&mut V> {
        if self.current.is_null() {
            return None;
        }
        // SAFETY: current is non-null and a valid tree node; &mut self ensures exclusivity.
        Some(unsafe { &mut (*node_deref_mut(self.current)).value })
    }

    /// Advances the cursor to the next element.
    pub fn advance(&mut self) -> bool {
        if !self.started {
            self.started = true;
            self.current = self.tree.leftmost;
            return !self.current.is_null();
        }
        if self.current.is_null() {
            return false;
        }
        // SAFETY: current is non-null and a valid tree node.
        self.current = unsafe { successor(self.current) };
        !self.current.is_null()
    }

    /// Removes the current element and advances to the next.
    pub fn remove(&mut self) -> Option<(K, V)> {
        if self.current.is_null() {
            return None;
        }
        let ptr = self.current;
        // SAFETY: ptr is non-null and a valid tree node.
        let next = unsafe { successor(ptr) };
        let result = self.tree.remove_node(self.slab, ptr);
        self.current = next;
        Some(result)
    }
}

// =============================================================================
// Drain
// =============================================================================

/// Draining iterator that removes and returns all key-value pairs in sorted order.
pub struct Drain<'a, K, V, C, S: SlabOps<RbNode<K, V>>> {
    tree: &'a mut RbTree<K, V, C>,
    slab: &'a S,
}

impl<K, V, C: Compare<K>, S: SlabOps<RbNode<K, V>>> Iterator for Drain<'_, K, V, C, S> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.tree.pop_first(self.slab)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.tree.len(), Some(self.tree.len()))
    }
}

impl<K, V, C: Compare<K>, S: SlabOps<RbNode<K, V>>> ExactSizeIterator for Drain<'_, K, V, C, S> {}

impl<K, V, C, S: SlabOps<RbNode<K, V>>> Drop for Drain<'_, K, V, C, S> {
    fn drop(&mut self) {
        self.tree.clear(self.slab);
    }
}
