# Changelog

All notable changes to nexus-collections are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Breaking

- **v2: slab types moved to `nexus_collections::slab::*`** behind the `slab` feature flag
  (enabled by default). Sub-modules expose associated types:
  `slab::list`, `slab::btree`, `slab::rbtree`, `slab::heap`, `slab::compare`.

  ```toml
  # unchanged for most users (slab is default)
  nexus-collections = "2.0"

  # opt-out of slab to avoid pulling nexus-slab
  nexus-collections = { version = "2.0", default-features = false }
  ```

  ```rust
  // before
  use nexus_collections::list::{List, ListNode};

  // after
  use nexus_collections::slab::list::{List, ListNode};
  // or primary types at slab root:
  use nexus_collections::slab::{List, ListNode};
  ```

## [1.1.4] and earlier

Earlier history is not documented in this CHANGELOG. See git history
and GitHub release notes for details.
