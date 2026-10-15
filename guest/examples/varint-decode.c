#include "../rt/om.h"
/* Unsigned LEB128 (varint) stream decoder.
 * Input: concatenated unsigned LEB128 encodings of u64 values.
 * Output: the decoded values, 8 bytes LE each.
 * Exit 1 (writing nothing) on a truncated encoding, an encoding longer
 * than 10 bytes, or a 10th byte carrying bits above bit 63 (it must be
 * 0 or 1). Non-canonical short forms (leading zero groups) are accepted.
 * Two passes: validate first so malformed input produces no output. */

/* Returns 1 if the whole stream is well-formed. */
static int validate(const uint8_t *in, uint64_t len) {
    uint64_t pos = 0;
    while (pos < len) {
        int nbytes = 0;
        for (;;) {
            if (pos >= len) return 0;          /* truncated */
            uint8_t b = in[pos++];
            nbytes++;
            if (nbytes == 10 && b > 1) return 0; /* overflow bits / cont. */
            if (!(b & 0x80)) break;
            if (nbytes == 10) return 0;        /* > 10 bytes */
        }
    }
    return 1;
}

int main(void) {
    const uint8_t *in = om_input();
    uint64_t len = om_input_len();
    if (!validate(in, len)) return 1;
    uint64_t pos = 0;
    while (pos < len) {
        uint64_t v = 0;
        unsigned shift = 0;
        for (;;) {
            uint8_t b = in[pos++];
            v |= (uint64_t)(b & 0x7F) << shift;
            if (!(b & 0x80)) break;
            shift += 7;
        }
        om_write_u64(v);
    }
    return 0;
}
