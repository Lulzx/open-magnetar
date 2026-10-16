//! SHA3-256 per FIPS 202: Keccak-f\[1600\], rate 1088 bits (136 bytes),
//! capacity 512 bits, delimited suffix `01` (pad byte `0x06`, final `0x80`).

const RC: [u64; 24] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808a,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808b,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008a,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000a,
    0x0000_0000_8000_808b,
    0x8000_0000_0000_008b,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800a,
    0x8000_0000_8000_000a,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

// Rotation offsets r[x][y], flattened as [x + 5*y].
const ROT: [u32; 25] = [
    0, 1, 62, 28, 27, //
    36, 44, 6, 55, 20, //
    3, 10, 43, 25, 39, //
    41, 45, 15, 21, 8, //
    18, 2, 61, 56, 14,
];

// Pi permutation: lane (x,y) moves to (y, 2x+3y mod 5); flattened target index.
const PI: [usize; 25] = [
    0, 10, 20, 5, 15, //
    16, 1, 11, 21, 6, //
    7, 17, 2, 12, 22, //
    23, 8, 18, 3, 13, //
    14, 24, 9, 19, 4,
];

fn keccak_f1600(state: &mut [u64; 25]) {
    for &rc in &RC {
        // Theta
        let mut c = [0u64; 5];
        for x in 0..5 {
            c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
        }
        let mut d = [0u64; 5];
        for x in 0..5 {
            d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        }
        for y in 0..5 {
            for x in 0..5 {
                state[x + 5 * y] ^= d[x];
            }
        }
        // Rho + Pi
        let mut b = [0u64; 25];
        for i in 0..25 {
            b[PI[i]] = state[i].rotate_left(ROT[i]);
        }
        // Chi
        for y in 0..5 {
            for x in 0..5 {
                state[x + 5 * y] =
                    b[x + 5 * y] ^ ((!b[(x + 1) % 5 + 5 * y]) & b[(x + 2) % 5 + 5 * y]);
            }
        }
        // Iota
        state[0] ^= rc;
    }
}

const RATE: usize = 136; // 1088 bits

#[inline]
pub fn sha3_256(data: &[u8]) -> [u8; 32] {
    sha3_256_slices(&[data])
}

pub fn sha3_256_slices(slices: &[&[u8]]) -> [u8; 32] {
    let mut state = [0u64; 25];
    let mut buf = [0u8; RATE];
    let mut buf_len = 0usize;

    for &slice in slices {
        let mut s = slice;
        if buf_len > 0 {
            let take = (RATE - buf_len).min(s.len());
            buf[buf_len..buf_len + take].copy_from_slice(&s[..take]);
            buf_len += take;
            s = &s[take..];
            if buf_len == RATE {
                absorb_block(&mut state, &buf);
                keccak_f1600(&mut state);
                buf_len = 0;
            }
        }
        let (chunks, rem) = s.as_chunks::<RATE>();
        for block in chunks {
            absorb_block(&mut state, block);
            keccak_f1600(&mut state);
        }
        if !rem.is_empty() {
            buf[..rem.len()].copy_from_slice(rem);
            buf_len = rem.len();
        }
    }

    // Final block with SHA3 padding: suffix 01 => 0x06 at the next byte,
    // 0x80 at the last rate byte (both may coincide: 0x86).
    buf[buf_len..RATE].fill(0);
    buf[buf_len] ^= 0x06;
    buf[RATE - 1] ^= 0x80;
    absorb_block(&mut state, &buf);
    keccak_f1600(&mut state);

    let mut out = [0u8; 32];
    for i in 0..4 {
        out[8 * i..8 * i + 8].copy_from_slice(&state[i].to_le_bytes());
    }
    out
}

fn absorb_block(state: &mut [u64; 25], block: &[u8]) {
    debug_assert_eq!(block.len(), RATE);
    for (i, lane) in block.as_chunks::<8>().0.iter().enumerate() {
        state[i] ^= u64::from_le_bytes(*lane);
    }
}
