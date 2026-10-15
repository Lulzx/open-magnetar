//! Multilinear extensions and eq (spec 03 §3.1, CONVENTIONS C2).
//! Mirrors `reference/openmagnetar/mle.py`.
//!
//! Indexing (C2): table entry `i` is identified with bits `(b_1, …, b_ℓ)`
//! where `b_1` is the least significant bit of `i`; MLE variable `x_1`
//! pairs with `b_1`. In characteristic 2, `eq(x, b) = Π_i (1 + x_i + b_i)`.
//!
//! Where Python raises `ValueError` on a shape mismatch (length mismatch,
//! odd table, wrong table length), these functions **panic**, matching the
//! `ValueError` → panic mapping used by `om-transcript`.

use om_field::K;

/// `eq(x, y) = Π_i (1 + x_i + y_i)` (characteristic 2).
///
/// # Panics
/// Panics if `x.len() != y.len()` (Python raises `ValueError`).
pub fn eq_eval(x: &[K], y: &[K]) -> K {
    assert_eq!(x.len(), y.len(), "eq_eval: length mismatch");
    let mut acc = K::ONE;
    for (&a, &b) in x.iter().zip(y) {
        acc *= K::ONE + a + b;
    }
    acc
}

/// The vector of length `2^len(r)` whose entry `i` is `eq(r, bits(i))`,
/// with bit `j` of `i` (LSB first) paired with `r[j]` (C2 order).
///
/// Built by `T ← [1]`, then for each `r_j`:
/// `T ← [T[i]·(1 + r_j)] ‖ [T[i]·r_j]`.
pub fn eq_table(r: &[K]) -> Vec<K> {
    let mut t = vec![K::ONE];
    for &rj in r {
        let mut next = Vec::with_capacity(2 * t.len());
        next.extend(t.iter().map(|&e| e * (K::ONE + rj)));
        next.extend(t.iter().map(|&e| e * rj));
        t = next;
    }
    t
}

/// Fix `x_1 = r`, halving the table:
/// `out[i] = T[2i] + r·(T[2i] + T[2i+1]) = (1+r)·T[2i] + r·T[2i+1]`.
///
/// # Panics
/// Panics if `table.len()` is odd (Python raises `ValueError`). An empty
/// table yields an empty table, as in Python.
pub fn bind_low(table: &[K], r: K) -> Vec<K> {
    assert!(
        table.len().is_multiple_of(2),
        "bind_low: table length must be even"
    );
    (0..table.len() / 2)
        .map(|i| table[2 * i] + r * (table[2 * i] + table[2 * i + 1]))
        .collect()
}

fn check_table_len(len: usize, num_vars: usize) {
    let expected = 1usize.checked_shl(num_vars as u32);
    assert_eq!(
        Some(len),
        expected,
        "mle_eval: table length must be 2^len(r)"
    );
}

/// The MLE evaluation `ṽ(r)`: bind `x_1, x_2, …` in turn and return the
/// single remaining entry.
///
/// # Panics
/// Panics if `table.len() != 2^r.len()` (Python raises `ValueError`).
pub fn mle_eval(table: &[K], r: &[K]) -> K {
    check_table_len(table.len(), r.len());
    let mut t = table.to_vec();
    for &ri in r {
        t = bind_low(&t, ri);
    }
    t[0]
}

/// [`mle_eval`] for a bit-valued table (`B^(2^ℓ)`).
///
/// Python's `mle_eval` accepts tables of `0`/`1` ints as well as `K`
/// elements (several modules pass bit tables, e.g. `[(a >> t) & 1 …]`), so
/// Rust provides this `&[bool]` variant; bits embed in `K` per C1
/// (`false ↦ 0`, `true ↦ 1`).
///
/// # Panics
/// Panics if `table.len() != 2^r.len()`.
pub fn mle_eval_bits(table: &[bool], r: &[K]) -> K {
    check_table_len(table.len(), r.len());
    let mut t: Vec<K> = table.iter().map(|&b| K::from_bit(b)).collect();
    for &ri in r {
        t = bind_low(&t, ri);
    }
    t[0]
}
