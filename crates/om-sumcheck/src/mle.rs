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
use rayon::prelude::*;

/// Tables at least this large use rayon; smaller ones stay sequential to
/// avoid thread-pool overhead in the many small sum-checks. All parallel
/// maps/reductions here are exact: elementwise maps preserve order and
/// `K` addition is XOR (associative and commutative).
pub(crate) const PAR_THRESHOLD: usize = 1 << 14;

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
    let n = r.len();
    if (1usize << n) >= PAR_THRESHOLD && n >= 4 {
        let h = (n / 2).clamp(2, 13);
        let lo = eq_table(&r[..h]);
        let hi = eq_table(&r[h..]);
        let lo_len = 1usize << h;
        let mut out = vec![K::ZERO; 1usize << n];
        out.par_chunks_mut(lo_len)
            .zip(hi.par_iter())
            .for_each(|(row, &h_val)| {
                for (dst, &l_val) in row.iter_mut().zip(&lo) {
                    *dst = l_val * h_val;
                }
            });
        return out;
    }
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
/// In-place form of [`bind_low`]: replaces `table` with its binding
/// at `r`, halving its length. Same arithmetic, no second allocation;
/// used on the memory-bound Spartan outer tables.
pub fn bind_low_in_place(table: &mut Vec<K>, r: K) {
    assert!(
        table.len().is_multiple_of(2),
        "bind_low: table length must be even"
    );
    let half = table.len() / 2;
    if table.len() >= PAR_THRESHOLD {
        const CHUNK: usize = 8192;
        table.par_chunks_mut(CHUNK).for_each(|chunk| {
            let h = chunk.len() / 2;
            for i in 0..h {
                let (a, b) = (chunk[2 * i], chunk[2 * i + 1]);
                chunk[i] = a + r * (a + b);
            }
        });
        let half_chunk = CHUNK / 2;
        let n_chunks = table.len().div_ceil(CHUNK);
        for c in 1..n_chunks {
            let src_start = c * CHUNK;
            let len = half_chunk.min(half - c * half_chunk);
            table.copy_within(src_start..src_start + len, c * half_chunk);
        }
    } else {
        for i in 0..half {
            table[i] = table[2 * i] + r * (table[2 * i] + table[2 * i + 1]);
        }
    }
    table.truncate(half);
}

/// A bit table packed into `u64` words: bit `i` is word `i / 64`,
/// bit `i % 64` (C2 index order, so word pairs pack directly into
/// `K` elements). The packed form of the `Vec<bool>` tables used
/// elsewhere: eight times smaller, and set bits can be iterated
/// without scanning zeros. Conversion both ways is exact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackedBits {
    words: Vec<u64>,
    len: usize,
}

impl PackedBits {
    /// All-zero table of `len` bits.
    pub fn zero(len: usize) -> Self {
        PackedBits {
            words: vec![0; len.div_ceil(64)],
            len,
        }
    }

    /// Construct directly from backing `u64` words and bit length `len`.
    /// Any bits at or beyond `len` in the final word are masked to zero.
    pub fn from_words(mut words: Vec<u64>, len: usize) -> Self {
        let needed = len.div_ceil(64);
        assert_eq!(
            words.len(),
            needed,
            "PackedBits::from_words: word count mismatch"
        );
        let rem = len % 64;
        if rem != 0
            && let Some(last) = words.last_mut()
        {
            *last &= (1u64 << rem) - 1;
        }
        PackedBits { words, len }
    }

    /// Pack a bool table.
    pub fn from_bools(bits: &[bool]) -> Self {
        let mut out = PackedBits::zero(bits.len());
        for (i, &b) in bits.iter().enumerate() {
            if b {
                out.set(i);
            }
        }
        out
    }

    /// Unpack to a bool table (the inverse of [`PackedBits::from_bools`]).
    pub fn to_bools(&self) -> Vec<bool> {
        (0..self.len).map(|i| self.bit(i)).collect()
    }

    /// Number of bits in the table.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether the table has no bits.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Bit `i`.
    ///
    /// # Panics
    /// Panics if `i >= len`.
    #[inline(always)]
    pub fn bit(&self, i: usize) -> bool {
        assert!(i < self.len, "PackedBits: index out of range");
        (self.words[i / 64] >> (i % 64)) & 1 == 1
    }

    /// Set bit `i` to 1.
    ///
    /// # Panics
    /// Panics if `i >= len`.
    #[inline(always)]
    pub fn set(&mut self, i: usize) {
        assert!(i < self.len, "PackedBits: index out of range");
        self.words[i / 64] |= 1u64 << (i % 64);
    }

    /// The backing words. Bits at or beyond `len` in the last word
    /// are zero.
    #[inline(always)]
    pub fn words(&self) -> &[u64] {
        &self.words
    }

    /// Mutable access to the backing words. Callers must keep bits at or
    /// beyond `len` in the last word zero.
    #[inline(always)]
    pub fn words_mut(&mut self) -> &mut [u64] {
        &mut self.words
    }

    /// Indices of the set bits, in increasing order.
    pub fn iter_ones(&self) -> impl Iterator<Item = usize> + '_ {
        self.words.iter().enumerate().flat_map(|(wi, &w)| {
            let mut w = w;
            std::iter::from_fn(move || {
                if w == 0 {
                    None
                } else {
                    let b = w.trailing_zeros() as usize;
                    w &= w - 1;
                    Some(wi * 64 + b)
                }
            })
        })
    }

    /// Number of set bits.
    pub fn count_ones(&self) -> usize {
        self.words.iter().map(|w| w.count_ones() as usize).sum()
    }
}

/// `MLE` evaluation of a packed bit table at `r`: the same value as
/// `mle_eval_bits` on the unpacked table, computed by summing `eq`
/// only over set bits.
///
/// # Panics
/// Panics if the table length is not `2^len(r)`.
pub fn mle_eval_packed(bits: &PackedBits, r: &[K]) -> K {
    assert_eq!(
        bits.len(),
        1usize << r.len(),
        "mle_eval_packed: table length must be 2^len(r)"
    );
    let e = eq_table(r);
    if e.len() >= PAR_THRESHOLD {
        bits.words()
            .par_iter()
            .enumerate()
            .map(|(wi, &w)| {
                let mut w = w;
                let mut acc = K::ZERO;
                let base = wi * 64;
                while w != 0 {
                    let b = w.trailing_zeros() as usize;
                    w &= w - 1;
                    acc += e[base + b];
                }
                acc
            })
            .reduce(|| K::ZERO, |a, b| a + b)
    } else {
        bits.iter_ones().fold(K::ZERO, |acc, i| acc + e[i])
    }
}

pub fn bind_low(table: &[K], r: K) -> Vec<K> {
    assert!(
        table.len().is_multiple_of(2),
        "bind_low: table length must be even"
    );
    if table.len() >= PAR_THRESHOLD {
        (0..table.len() / 2)
            .into_par_iter()
            .map(|i| table[2 * i] + r * (table[2 * i] + table[2 * i + 1]))
            .collect()
    } else {
        (0..table.len() / 2)
            .map(|i| table[2 * i] + r * (table[2 * i] + table[2 * i + 1]))
            .collect()
    }
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
    let Some((&r0, rest)) = r.split_first() else {
        return table[0];
    };
    let mut t = bind_low(table, r0);
    for &ri in rest {
        bind_low_in_place(&mut t, ri);
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
    let e = eq_table(r);
    if table.len() >= PAR_THRESHOLD {
        table
            .par_iter()
            .zip(e.par_iter())
            .filter_map(|(&b, &ei)| if b { Some(ei) } else { None })
            .reduce(|| K::ZERO, |a, b| a + b)
    } else {
        let mut acc = K::ZERO;
        for (&b, &ei) in table.iter().zip(&e) {
            if b {
                acc += ei;
            }
        }
        acc
    }
}
