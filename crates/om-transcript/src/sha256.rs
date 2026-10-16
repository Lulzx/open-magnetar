//! SHA-256 per FIPS 180-4, from scratch.

const K256: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

const IV256: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

#[inline]
pub fn digest(data: &[u8]) -> [u8; 32] {
    digest_slices(&[data])
}

pub fn digest_slices(slices: &[&[u8]]) -> [u8; 32] {
    let mut h = IV256;
    let mut buf = [0u8; 64];
    let mut buf_len = 0usize;
    let mut total_len = 0u64;

    for &slice in slices {
        total_len = total_len.wrapping_add(slice.len() as u64);
        let mut s = slice;
        if buf_len > 0 {
            let take = (64 - buf_len).min(s.len());
            buf[buf_len..buf_len + take].copy_from_slice(&s[..take]);
            buf_len += take;
            s = &s[take..];
            if buf_len == 64 {
                compress_block(&mut h, &buf);
                buf_len = 0;
            }
        }
        let (blocks, rem) = s.as_chunks::<64>();
        for block in blocks {
            compress_block(&mut h, block);
        }
        if !rem.is_empty() {
            buf[..rem.len()].copy_from_slice(rem);
            buf_len = rem.len();
        }
    }

    // Padding: 0x80, zeros, 64-bit big-endian bit length, to a multiple of 64.
    let bit_len = total_len.wrapping_mul(8);
    buf[buf_len] = 0x80;
    buf_len += 1;
    if buf_len > 56 {
        buf[buf_len..64].fill(0);
        compress_block(&mut h, &buf);
        buf[..56].fill(0);
    } else {
        buf[buf_len..56].fill(0);
    }
    buf[56..64].copy_from_slice(&bit_len.to_be_bytes());
    compress_block(&mut h, &buf);

    let mut out = [0u8; 32];
    for (i, word) in h.iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

#[inline(always)]
fn compress_block(h: &mut [u32; 8], block: &[u8; 64]) {
    #[cfg(all(target_arch = "aarch64", target_feature = "sha2"))]
    {
        // SAFETY: `sha2` target feature is enabled at compile time.
        unsafe { compress_block_aarch64(h, block) };
        return;
    }
    #[cfg(all(target_arch = "aarch64", not(target_feature = "sha2")))]
    {
        if std::arch::is_aarch64_feature_detected!("sha2") {
            // SAFETY: `sha2` feature was just detected at runtime.
            unsafe { compress_block_aarch64(h, block) };
            return;
        }
    }
    #[allow(unreachable_code)]
    compress_block_portable(h, block);
}

pub(crate) fn compress_block_portable(h: &mut [u32; 8], block: &[u8; 64]) {
    let mut w = [0u32; 64];
    for i in 0..16 {
        w[i] = u32::from_be_bytes([
            block[4 * i],
            block[4 * i + 1],
            block[4 * i + 2],
            block[4 * i + 3],
        ]);
    }
    for i in 16..64 {
        let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
        let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16]
            .wrapping_add(s0)
            .wrapping_add(w[i - 7])
            .wrapping_add(s1);
    }
    let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh) =
        (h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7]);
    for i in 0..64 {
        let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ ((!e) & g);
        let t1 = hh
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add(K256[i])
            .wrapping_add(w[i]);
        let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = s0.wrapping_add(maj);
        hh = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }
    h[0] = h[0].wrapping_add(a);
    h[1] = h[1].wrapping_add(b);
    h[2] = h[2].wrapping_add(c);
    h[3] = h[3].wrapping_add(d);
    h[4] = h[4].wrapping_add(e);
    h[5] = h[5].wrapping_add(f);
    h[6] = h[6].wrapping_add(g);
    h[7] = h[7].wrapping_add(hh);
}

#[cfg(target_arch = "aarch64")]
#[inline]
#[target_feature(enable = "sha2,neon")]
unsafe fn compress_block_aarch64(h: &mut [u32; 8], block: &[u8; 64]) {
    use core::arch::aarch64::{
        vaddq_u32, vld1q_u8, vld1q_u32, vreinterpretq_u32_u8, vrev32q_u8, vsha256h2q_u32,
        vsha256hq_u32, vsha256su0q_u32, vsha256su1q_u32, vst1q_u32,
    };

    // SAFETY: `h` has 8 `u32` elements and `block` has 64 `u8` elements;
    // `K256` has 64 `u32` elements. All pointer offsets are in-bounds.
    unsafe {
        let abcd_orig = vld1q_u32(h.as_ptr());
        let efgh_orig = vld1q_u32(h.as_ptr().add(4));
        let mut abcd = abcd_orig;
        let mut efgh = efgh_orig;

        let mut w0 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block.as_ptr())));
        let mut w1 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block.as_ptr().add(16))));
        let mut w2 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block.as_ptr().add(32))));
        let mut w3 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block.as_ptr().add(48))));

        macro_rules! round4 {
            ($w:ident, $idx:expr) => {{
                let wk = vaddq_u32($w, vld1q_u32(K256.as_ptr().add($idx)));
                let prev_abcd = abcd;
                abcd = vsha256hq_u32(abcd, efgh, wk);
                efgh = vsha256h2q_u32(efgh, prev_abcd, wk);
            }};
            ($w0:ident, $w1:ident, $w2:ident, $w3:ident, $idx:expr) => {{
                round4!($w0, $idx);
                $w0 = vsha256su1q_u32(vsha256su0q_u32($w0, $w1), $w2, $w3);
            }};
        }

        round4!(w0, w1, w2, w3, 0);
        round4!(w1, w2, w3, w0, 4);
        round4!(w2, w3, w0, w1, 8);
        round4!(w3, w0, w1, w2, 12);

        round4!(w0, w1, w2, w3, 16);
        round4!(w1, w2, w3, w0, 20);
        round4!(w2, w3, w0, w1, 24);
        round4!(w3, w0, w1, w2, 28);

        round4!(w0, w1, w2, w3, 32);
        round4!(w1, w2, w3, w0, 36);
        round4!(w2, w3, w0, w1, 40);
        round4!(w3, w0, w1, w2, 44);

        round4!(w0, 48);
        round4!(w1, 52);
        round4!(w2, 56);
        round4!(w3, 60);

        abcd = vaddq_u32(abcd, abcd_orig);
        efgh = vaddq_u32(efgh, efgh_orig);

        vst1q_u32(h.as_mut_ptr(), abcd);
        vst1q_u32(h.as_mut_ptr().add(4), efgh);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn aarch64_sha2_matches_portable() {
        if !std::arch::is_aarch64_feature_detected!("sha2") {
            return;
        }
        let mut h_port = IV256;
        let mut h_hw = IV256;
        for b in 0..32u8 {
            let mut block = [0u8; 64];
            for (i, byte) in block.iter_mut().enumerate() {
                *byte = b.wrapping_mul(37).wrapping_add(i as u8);
            }
            compress_block_portable(&mut h_port, &block);
            // SAFETY: `sha2` was detected just above.
            unsafe { compress_block_aarch64(&mut h_hw, &block) };
            assert_eq!(h_hw, h_port);
        }
    }

    #[test]
    fn digest_slices_matches_concatenated() {
        let a = b"hello ";
        let b = &[0u8; 73];
        let c = b"world of open magnetar";
        let mut full = Vec::new();
        full.extend_from_slice(a);
        full.extend_from_slice(b);
        full.extend_from_slice(c);
        assert_eq!(digest_slices(&[a, b, c]), digest(&full));
    }
}
