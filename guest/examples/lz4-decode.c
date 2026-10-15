#include "../rt/om.h"
/* LZ4 block-format decoder (raw block, no frame header / no content size).
 * Per sequence: token byte; literal length = high nibble (15 => extension
 * bytes follow, summed, a byte < 255 ends the run); that many literal
 * bytes; if input is exhausted here the block ends (last sequence is
 * literals-only); else a 2-byte little-endian match offset and a match
 * length = low nibble (+ extension bytes if 15) + 4, copied byte-by-byte
 * from output[pos - offset] (overlapping copies allowed, per spec).
 * Input: one compressed block. Output: the decompressed bytes.
 * Caps: decompressed size <= 65536 bytes (static buffer). Exit 1 on
 * truncated input, an offset of 0 or beyond the bytes produced so far,
 * or output above the cap. */

#define OUT_CAP 65536
static uint8_t outbuf[OUT_CAP];

/* Read an extension-byte run starting at *pos; adds to *len_acc.
 * Returns 0 on truncation. */
static int read_ext(const uint8_t *in, uint64_t len, uint64_t *pos, uint64_t *acc) {
    for (;;) {
        if (*pos >= len) return 0;
        uint8_t b = in[(*pos)++];
        *acc += b;
        if (b != 255) return 1;
    }
}

int main(void) {
    const uint8_t *in = om_input();
    uint64_t len = om_input_len();
    uint64_t pos = 0, opos = 0;
    while (pos < len) {
        uint8_t token = in[pos++];
        uint64_t litlen = token >> 4;
        if (litlen == 15 && !read_ext(in, len, &pos, &litlen)) return 1;
        if (pos + litlen > len || opos + litlen > OUT_CAP) return 1;
        for (uint64_t i = 0; i < litlen; i++) outbuf[opos++] = in[pos++];
        if (pos >= len) break; /* final literals-only sequence */
        if (pos + 2 > len) return 1;
        uint64_t offset = (uint64_t)in[pos] | ((uint64_t)in[pos + 1] << 8);
        pos += 2;
        if (offset == 0 || offset > opos) return 1;
        uint64_t matchlen = token & 15;
        if (matchlen == 15 && !read_ext(in, len, &pos, &matchlen)) return 1;
        matchlen += 4;
        if (opos + matchlen > OUT_CAP) return 1;
        uint64_t mstart = opos - offset;
        for (uint64_t i = 0; i < matchlen; i++) outbuf[opos++] = outbuf[mstart++];
    }
    om_write(outbuf, (size_t)opos);
    return 0;
}
