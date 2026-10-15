/* open-magnetar guest I/O helpers (informative tooling).
 * Input region : word 0 = byte length n, bytes 0..n-1 little-endian from word 1.
 * Output region: same encoding; write with om_write (append) only. Bytes beyond
 * the length MUST stay zero (RAM starts zero, so append-only keeps this true). */
#ifndef OM_H
#define OM_H
#include <stdint.h>
#include <stddef.h>

extern char __input_base[], __output_base[], __heap_start[], __heap_end[];

static inline uint64_t om_input_len(void) { return *(volatile uint64_t *)__input_base; }
static inline const uint8_t *om_input(void) { return (const uint8_t *)__input_base + 8; }

static inline void om_write(const void *p, size_t n) {
    volatile uint64_t *len = (volatile uint64_t *)__output_base;
    uint8_t *dst = (uint8_t *)__output_base + 8 + *len;
    const uint8_t *src = (const uint8_t *)p;
    for (size_t i = 0; i < n; i++) dst[i] = src[i];
    *len += n;
}
static inline void om_write_u64(uint64_t v) {
    uint8_t b[8];
    for (int i = 0; i < 8; i++) b[i] = (uint8_t)(v >> (8 * i));
    om_write(b, 8);
}
static inline uint64_t om_read_u64(size_t off) {
    uint64_t v = 0;
    for (int i = 7; i >= 0; i--) v = (v << 8) | om_input()[off + i];
    return v;
}
#endif
