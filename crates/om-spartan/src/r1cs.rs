//! Sparse R1CS / SIMD R1CS structures (spec 06 §6.1–6.2).
//! Mirrors `reference/openmagnetar/r1cs.py`.
//!
//! A structure has `2^rho` rows and `2^nu` columns. The vector
//! `z = (w, 1, x)` has length `2^nu`: `w` occupies indices
//! `[0, 2^(nu-1))`, index `2^(nu-1)` holds the constant `1`, then the
//! public input `x`, then zeros. Entries live in `B`
//! ([`RelationField::B`], values 0/1) or `K` ([`RelationField::K`]).
//!
//! Where Python raises `ValueError` (programmer errors: out-of-range
//! entries, dimension mismatches, malformed witness) these functions
//! **panic**, matching the mapping already used by `om-transcript` and
//! `om-sumcheck`. Bit vectors are `&[bool]` (Python `list[int]` of 0/1),
//! and public inputs are `K` elements (Python caller-side `0`/`1` ints
//! are converted with [`K::from_bit`]).

use std::collections::BTreeMap;

use om_field::K;
use om_sumcheck::eq_table;

/// The field a relation's matrix entries live in (Python's `"B"` / `"K"`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RelationField {
    /// Entries in `B = GF(2)`: every non-zero entry is `1`.
    B,
    /// Entries in `K = GF(2^128)`.
    K,
}

/// A `2^rho x 2^nu` sparse matrix: the list of non-zero entries
/// `(row, column, value)`, sorted by `(row, column)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseMatrix {
    pub rho: usize,
    pub nu: usize,
    entries: Vec<(usize, usize, K)>,
}

impl SparseMatrix {
    /// Build from `((row, col), value)` entries. Zero values are dropped
    /// (as in Python); on duplicate `(row, col)` keys the last wins, as
    /// with a Python dict literal.
    ///
    /// # Panics
    /// Panics if an entry is out of range (Python raises `ValueError`).
    pub fn new(
        rho: usize,
        nu: usize,
        entries: impl IntoIterator<Item = ((usize, usize), K)>,
    ) -> Self {
        let mut map = BTreeMap::new();
        for ((r, c), v) in entries {
            assert!(
                r < (1usize << rho) && c < (1usize << nu),
                "matrix entry out of range"
            );
            if !v.is_zero() {
                map.insert((r, c), v);
            } else {
                map.remove(&(r, c));
            }
        }
        SparseMatrix {
            rho,
            nu,
            entries: map.into_iter().map(|((r, c), v)| (r, c, v)).collect(),
        }
    }

    /// The non-zero entries as `(row, column, value)` triples, sorted by
    /// `(row, column)` (Python's `entries` dict, as triples).
    pub fn entries(&self) -> &[(usize, usize, K)] {
        &self.entries
    }

    /// `M z` for a `K`-valued `z`.
    ///
    /// # Panics
    /// Panics if `z` is shorter than some entry's column index (Python
    /// raises `IndexError`).
    pub fn mul_vec(&self, z: &[K]) -> Vec<K> {
        let mut out = vec![K::ZERO; 1 << self.rho];
        for &(r, c, v) in &self.entries {
            out[r] += v * z[c];
        }
        out
    }

    /// `M z` for a bit-valued `z`: XOR of the selected entries, with no
    /// `K` multiplication (spec 06 §6.2).
    ///
    /// # Panics
    /// Panics if `z` is shorter than some entry's column index.
    pub fn mul_vec_bits(&self, z: &[bool]) -> Vec<K> {
        let mut out = vec![K::ZERO; 1 << self.rho];
        for &(r, c, v) in &self.entries {
            if z[c] {
                out[r] += v;
            }
        }
        out
    }

    /// `M~(r_row, r_col) = sum_{(r,c)} M[r][c] eq(r_row, r) eq(r_col, c)`,
    /// in `O(nnz)` after the eq tables.
    ///
    /// # Panics
    /// Panics if `r_row.len() != rho` or `r_col.len() != nu` (Python
    /// raises `ValueError`).
    pub fn mle(&self, r_row: &[K], r_col: &[K]) -> K {
        assert!(
            r_row.len() == self.rho && r_col.len() == self.nu,
            "point length mismatch"
        );
        let (er, ec) = (eq_table(r_row), eq_table(r_col));
        let mut acc = K::ZERO;
        for &(r, c, v) in &self.entries {
            acc += v * er[r] * ec[c];
        }
        acc
    }

    /// Table over columns: `c -> sum_r eq(r_row, r) M[r][c]`
    /// (`= M~(r_row, c)`).
    ///
    /// # Panics
    /// Panics if `r_row.len() != rho`.
    pub fn fold_rows(&self, r_row: &[K]) -> Vec<K> {
        assert_eq!(r_row.len(), self.rho, "point length mismatch");
        let er = eq_table(r_row);
        let mut out = vec![K::ZERO; 1 << self.nu];
        for &(r, c, v) in &self.entries {
            out[c] += v * er[r];
        }
        out
    }
}

/// A base R1CS structure `s = (A, B, C)` (spec 06 §6.1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R1CS {
    pub field: RelationField,
    pub rho: usize,
    pub nu: usize,
    pub a: SparseMatrix,
    pub b: SparseMatrix,
    pub c: SparseMatrix,
}

impl R1CS {
    /// # Panics
    /// Panics if a matrix's `(rho, nu)` differs from the structure's, or
    /// if a `B`-relation has an entry outside `{0, 1}` (Python raises
    /// `ValueError`; spec 06 §6.4 makes the latter a verifying-key check).
    pub fn new(
        field: RelationField,
        rho: usize,
        nu: usize,
        a: SparseMatrix,
        b: SparseMatrix,
        c: SparseMatrix,
    ) -> Self {
        let s = R1CS {
            field,
            rho,
            nu,
            a,
            b,
            c,
        };
        for m in s.mats() {
            assert!((m.rho, m.nu) == (rho, nu), "matrix dimension mismatch");
            assert!(
                field != RelationField::B || m.entries().iter().all(|&(_, _, v)| v.value() <= 1),
                "B-relation entries must be 0/1"
            );
        }
        s
    }

    /// The three matrices `(A, B, C)`, in order.
    pub fn mats(&self) -> [&SparseMatrix; 3] {
        [&self.a, &self.b, &self.c]
    }

    /// Whether every row of this instance is satisfied:
    /// `(A z)_j * (B z)_j == (C z)_j` for all `j`.
    pub fn check_instance(&self, z: &[K]) -> bool {
        let [a, b, c] = self.mats().map(|m| m.mul_vec(z));
        a.iter().zip(&b).zip(&c).all(|((&x, &y), &w)| x * y == w)
    }
}

/// `z = (w, 1, x)`, zero padded to `2^nu`, as `K` elements.
/// `w.len()` must be `2^(nu-1)`; `1 + x.len() <= 2^(nu-1)`.
///
/// # Panics
/// Panics if `nu == 0`, if `w` has the wrong length, or if the public
/// input is too long (Python raises `ValueError`).
pub fn build_z(w: &[bool], x: &[K], nu: usize) -> Vec<K> {
    assert!(nu >= 1, "nu must be at least 1");
    let half = 1usize << (nu - 1);
    assert_eq!(
        w.len(),
        half,
        "witness must have exactly 2^(nu-1) entries (pad with zeros)"
    );
    assert!(x.len() < half, "public input too long");
    let mut z: Vec<K> = w.iter().map(|&bit| K::from_bit(bit)).collect();
    z.push(K::ONE);
    z.extend_from_slice(x);
    z.resize(1 << nu, K::ZERO);
    z
}

/// `(1, x)` zero padded to `2^(nu-1)` (the public part `P` of spec 06
/// §6.1).
///
/// # Panics
/// Panics if `nu == 0` or if the public input is too long.
pub fn public_part(x: &[K], nu: usize) -> Vec<K> {
    assert!(nu >= 1, "nu must be at least 1");
    let half = 1usize << (nu - 1);
    assert!(x.len() < half, "public input too long");
    let mut p = vec![K::ONE];
    p.extend_from_slice(x);
    p.resize(half, K::ZERO);
    p
}

/// Check that every row of `w` has exactly `2^(nu-1)` entries. (Python
/// also checks that entries are bits `0`/`1`, which `bool` enforces by
/// construction.)
///
/// # Panics
/// Panics if `nu == 0` or a row has the wrong length (Python raises
/// `ValueError`).
pub fn check_witness_bits(w: &[Vec<bool>], nu: usize) {
    assert!(nu >= 1, "nu must be at least 1");
    for row in w {
        assert_eq!(
            row.len(),
            1usize << (nu - 1),
            "W must be a bit matrix with 2^(nu-1) columns"
        );
    }
}

/// Whether all relations hold on every row (the shared-witness SIMD
/// relation of paper §5.1, spec 06 §6.1).
///
/// # Panics
/// Panics if `structs` is empty, if `w` and `x` have different row
/// counts, or if a witness row is malformed (Python raises
/// `ValueError` / `IndexError`).
pub fn simd_satisfied(structs: &[R1CS], w: &[Vec<bool>], x: &[Vec<K>]) -> bool {
    assert_eq!(w.len(), x.len(), "W and X must have one row per instance");
    let nu = structs.first().expect("no relations").nu;
    check_witness_bits(w, nu);
    structs.iter().all(|s| {
        w.iter()
            .zip(x)
            .all(|(wi, xi)| s.check_instance(&build_z(wi, xi, nu)))
    })
}

/// Row-major flattening of `W`: index = column + `2^(nu-1)` * instance
/// (CONVENTIONS C2 witness-matrix exception).
pub fn flatten_w(w: &[Vec<bool>]) -> Vec<bool> {
    w.iter().flat_map(|row| row.iter().copied()).collect()
}
