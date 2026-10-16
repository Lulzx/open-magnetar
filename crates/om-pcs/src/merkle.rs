//! Merkle trees per spec 04 §4.2. Mirrors `reference/openmagnetar/merkle.py`.
//!
//! Digests are `Vec<u8>` because the configured hash may have a 48-byte
//! output (sha384), as Python `bytes` does.

use std::collections::{BTreeMap, BTreeSet};

use om_sumcheck::VerificationError;
use om_transcript::Hasher;
use rayon::prelude::*;

/// Layers with at least this many hashes are built in parallel (hashing is
/// comparatively expensive, so the threshold is lower than for field maps;
/// digest order is preserved by `collect`).
const PAR_HASHES: usize = 1024;

/// A hash digest (length depends on the configured [`Hasher`]).
pub type Digest = Vec<u8>;

/// Domain byte for leaf hashing (`0x00`).
pub const LEAF: u8 = 0x00;
/// Domain byte for node hashing (`0x01`).
pub const NODE: u8 = 0x01;
/// Domain byte for the empty/padding hash (`0x02`).
pub const EMPTY: u8 = 0x02;

/// `H(0x00 || data)`.
#[inline]
pub fn hash_leaf(h: Hasher, data: &[u8]) -> Digest {
    h.digest_slices(&[&[LEAF], data])
}

/// `H(0x00 || data)` written directly into `out` (`h.digest_size()` bytes).
#[inline]
pub fn hash_leaf_into(h: Hasher, data: &[u8], out: &mut [u8]) {
    h.digest_slices_into(&[&[LEAF], data], out);
}

/// `H(0x01 || left || right)`.
#[inline]
pub fn hash_node(h: Hasher, left: &[u8], right: &[u8]) -> Digest {
    let mut out = vec![0u8; h.digest_size()];
    hash_node_into(h, left, right, &mut out);
    out
}

/// `H(0x01 || left || right)` written directly into `out` (`h.digest_size()` bytes).
#[inline]
pub fn hash_node_into(h: Hasher, left: &[u8], right: &[u8], out: &mut [u8]) {
    h.hash_merkle_node_into(left, right, out);
}

/// `H(0x02)`, the padding entry.
pub fn empty_hash(h: Hasher) -> Digest {
    h.digest(&[EMPTY])
}

/// Depth `ceil(log2(num_leaves))` (`0` for one leaf).
///
/// # Panics
/// Panics if `num_leaves < 1` (Python raises `ValueError`).
pub fn tree_depth(num_leaves: usize) -> usize {
    assert!(num_leaves >= 1, "a Merkle tree needs at least one leaf");
    (usize::BITS - (num_leaves - 1).leading_zeros()) as usize
}

/// A binary Merkle tree over byte-string leaves (spec 04 §4.2).
/// Each layer is stored as a contiguous `Vec<u8>` of `num_nodes * h.digest_size()`
/// bytes to avoid millions of small heap allocations on large trees.
#[derive(Clone, Debug)]
pub struct MerkleTree {
    /// The hash profile.
    pub h: Hasher,
    /// Number of real (unpadded) leaves.
    pub num_leaves: usize,
    /// Contiguous hash layers (`count * h.digest_size()` bytes per layer),
    /// leaves first; the last layer holds the single root digest.
    flat_layers: Vec<Vec<u8>>,
}

impl MerkleTree {
    /// Build a tree over `leaves`, padding on the right with [`empty_hash`].
    ///
    /// # Panics
    /// Panics if `leaves` is empty.
    pub fn new(h: Hasher, leaves: &[Vec<u8>]) -> Self {
        assert!(!leaves.is_empty(), "a Merkle tree needs at least one leaf");
        let dsz = h.digest_size();
        let mut flat = vec![0u8; leaves.len() * dsz];
        if leaves.len() >= PAR_HASHES {
            flat.par_chunks_mut(dsz)
                .zip(leaves.par_iter())
                .for_each(|(out, x)| hash_leaf_into(h, x, out));
        } else {
            for (out, x) in flat.chunks_mut(dsz).zip(leaves.iter()) {
                hash_leaf_into(h, x, out);
            }
        }
        Self::from_flat_leaf_hashes(h, leaves.len(), flat)
    }

    /// Build a tree from already hashed leaves (`hash_leaf` of each
    /// leaf, in order): the same tree as [`MerkleTree::new`] on the
    /// leaves, without holding the leaf bytes.
    ///
    /// # Panics
    /// Panics if `layer` is empty.
    pub fn from_leaf_hashes(h: Hasher, layer: Vec<Digest>) -> Self {
        assert!(!layer.is_empty(), "a Merkle tree needs at least one leaf");
        let num_leaves = layer.len();
        let dsz = h.digest_size();
        let mut flat = Vec::with_capacity(num_leaves * dsz);
        for d in layer {
            debug_assert_eq!(d.len(), dsz);
            flat.extend_from_slice(&d);
        }
        Self::from_flat_leaf_hashes(h, num_leaves, flat)
    }

    /// Build a tree from a contiguous byte buffer `flat_layer` of
    /// `num_leaves * h.digest_size()` leaf hash bytes.
    ///
    /// # Panics
    /// Panics if `num_leaves == 0` or `flat_layer.len() != num_leaves * h.digest_size()`.
    pub fn from_flat_leaf_hashes(h: Hasher, num_leaves: usize, mut flat_layer: Vec<u8>) -> Self {
        let dsz = h.digest_size();
        assert!(num_leaves >= 1, "a Merkle tree needs at least one leaf");
        assert_eq!(flat_layer.len(), num_leaves * dsz);
        let depth = tree_depth(num_leaves);
        let padded = 1usize << depth;
        if padded > num_leaves {
            let empty = empty_hash(h);
            flat_layer.reserve((padded - num_leaves) * dsz);
            for _ in num_leaves..padded {
                flat_layer.extend_from_slice(&empty);
            }
        }
        let mut flat_layers = Vec::with_capacity(depth + 1);
        flat_layers.push(flat_layer);
        while flat_layers.last().expect("layers").len() > dsz {
            let prev = flat_layers.last().expect("layers");
            let next_nodes = prev.len() / (2 * dsz);
            let mut next = vec![0u8; next_nodes * dsz];
            if next_nodes >= PAR_HASHES {
                next.par_chunks_mut(dsz)
                    .zip(prev.par_chunks(2 * dsz))
                    .for_each(|(out, pair)| {
                        hash_node_into(h, &pair[..dsz], &pair[dsz..], out);
                    });
            } else {
                for (out, pair) in next.chunks_mut(dsz).zip(prev.chunks(2 * dsz)) {
                    hash_node_into(h, &pair[..dsz], &pair[dsz..], out);
                }
            }
            flat_layers.push(next);
        }
        MerkleTree {
            h,
            num_leaves,
            flat_layers,
        }
    }

    /// The root digest.
    pub fn root(&self) -> Digest {
        self.flat_layers.last().expect("layers").clone()
    }

    /// Deduplicated multi-path for strictly ascending `indices` (§4.2).
    ///
    /// # Errors
    /// Returns [`VerificationError`] on an empty, non-ascending, or
    /// out-of-range index set (as Python `MerkleTree.open` raises).
    pub fn open(&self, indices: &[usize]) -> Result<Vec<Digest>, VerificationError> {
        check_indices(indices, self.num_leaves)?;
        let dsz = self.h.digest_size();
        let mut auth = Vec::new();
        let mut cur: Vec<usize> = indices.to_vec();
        for lvl in 0..self.flat_layers.len() - 1 {
            let layer = &self.flat_layers[lvl];
            let s: BTreeSet<usize> = cur.iter().copied().collect();
            for &i in &cur {
                let sib = i ^ 1;
                if !s.contains(&sib) {
                    auth.push(layer[sib * dsz..(sib + 1) * dsz].to_vec());
                }
            }
            let next: BTreeSet<usize> = cur.iter().map(|&i| i >> 1).collect();
            cur = next.into_iter().collect();
        }
        Ok(auth)
    }

    /// Alias for [`MerkleTree::open`].
    pub fn prove(&self, indices: &[usize]) -> Result<Vec<Digest>, VerificationError> {
        self.open(indices)
    }
}

/// Reject empty, non-strictly-ascending, or out-of-range index sets.
pub fn check_indices(indices: &[usize], num_leaves: usize) -> Result<(), VerificationError> {
    if indices.is_empty() {
        return Err(VerificationError::new("empty index set"));
    }
    let mut prev: Option<usize> = None;
    for &i in indices {
        if i >= num_leaves || prev.is_some_and(|p| p >= i) {
            return Err(VerificationError::new(
                "indices must be strictly ascending and in range",
            ));
        }
        prev = Some(i);
    }
    Ok(())
}

/// Verify a deduplicated multi-opening (§4.2): exact `auth` consumption and
/// final node equal to `root`.
///
/// # Errors
/// Returns [`VerificationError`] on any rejection rule of §4.2.
#[allow(clippy::too_many_arguments)]
pub fn verify_multi(
    h: Hasher,
    root: &[u8],
    num_leaves: usize,
    indices: &[usize],
    leaves: &[Vec<u8>],
    auth: &[Digest],
) -> Result<(), VerificationError> {
    check_indices(indices, num_leaves)?;
    if leaves.len() != indices.len() {
        return Err(VerificationError::new("leaf count mismatch"));
    }
    let depth = tree_depth(num_leaves);
    let mut nodes: BTreeMap<usize, Digest> = indices
        .iter()
        .zip(leaves)
        .map(|(&i, x)| (i, hash_leaf(h, x)))
        .collect();
    let mut pos = 0usize;
    let mut cur: Vec<usize> = indices.to_vec();
    for _ in 0..depth {
        let s: BTreeSet<usize> = cur.iter().copied().collect();
        let mut sib: BTreeMap<usize, Digest> = BTreeMap::new();
        for &i in &cur {
            if !s.contains(&(i ^ 1)) {
                if pos >= auth.len() {
                    return Err(VerificationError::new("authentication data too short"));
                }
                sib.insert(i ^ 1, auth[pos].clone());
                pos += 1;
            }
        }
        let mut nxt: BTreeMap<usize, Digest> = BTreeMap::new();
        for &i in &cur {
            let p = i >> 1;
            if nxt.contains_key(&p) {
                continue;
            }
            let (l, r) = (i & !1, i | 1);
            let lv = nodes.get(&l).or_else(|| sib.get(&l)).expect("sibling");
            let rv = nodes.get(&r).or_else(|| sib.get(&r)).expect("sibling");
            nxt.insert(p, hash_node(h, lv, rv));
        }
        nodes = nxt;
        cur = nodes.keys().copied().collect();
    }
    if pos != auth.len() {
        return Err(VerificationError::new("authentication data too long"));
    }
    if nodes.get(&0).map(Vec::as_slice) != Some(root) {
        return Err(VerificationError::new("Merkle root mismatch"));
    }
    Ok(())
}
