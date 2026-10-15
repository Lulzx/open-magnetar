#include "../rt/om.h"
/* Minimal EVM interpreter guest + embedded ERC-20 transfer runtime.
 * This is a faithful-in-spirit port of the paper's evm-erc20-transfer
 * workload shape (an EVM interpreter as the guest). Simplifications vs
 * mainnet EVM, all deliberate and documented:
 *  - Storage is 1024 slots of u256 in static RAM; the slot index is the
 *    LOW 64 BITS of the storage key (keys with equal low bits alias, and
 *    a low half >= 1024 is an exceptional halt). No hashing of mapping
 *    keys, no accounts, no gas (a 1,000,000-step cap replaces it).
 *  - Memory is a fixed 8192-byte array; accesses beyond it halt instead
 *    of expanding memory. Stack depth cap is 256 (EVM: 1024).
 *  - Opcode subset: STOP ADD MUL SUB LT GT EQ ISZERO AND OR XOR SHL SHR
 *    CALLDATALOAD CALLDATASIZE MLOAD MSTORE SLOAD SSTORE JUMP JUMPI
 *    JUMPDEST PUSH1-PUSH32 DUP1-DUP4 SWAP1-SWAP2 RETURN REVERT.
 * Arithmetic is full 256-bit (4 u64 limbs); MUL is hand shift-and-add
 * (32-bit halves) because the guest target is strict RV64I (no M ops).
 *
 * Input framing (exit 1 if malformed; this is guest framing, not EVM):
 *   u64 code_len; if 0, the embedded ERC-20 transfer runtime below is
 *   used, else code_len bytes of bytecode follow (<= 4096).
 *   u64 calldata_len (<= 4096), calldata bytes.
 *   u64 n_storage (<= 1024), then per entry: u64 slot, 32-byte BE value.
 * Output:
 *   u64 status (1 = STOP/RETURN, 0 = REVERT or exceptional halt),
 *   u64 return_len, return bytes (RETURN/REVERT data, else empty),
 *   u64 n_nonzero_slots, then per nonzero slot ascending:
 *   u64 slot, 32-byte BE value. Storage is rolled back on failure.
 *
 * Embedded runtime (75 bytes) semantics: calldata is a 4-byte selector
 * (ignored) then three 32-byte BE words: from_slot, to_slot, amount.
 * Balances live directly in storage slots from_slot/to_slot. If
 * balance[from] < amount it returns a 32-byte zero word; else it moves
 * the amount and returns a 32-byte word 1. The byte array below was
 * hand-assembled; the Python test in /tmp/test_guests.py carries the
 * identical byte string (EVM_RUNTIME_HEX) and cross-checks both the
 * embedded path and the same bytes injected as code. */

#define STACK_CAP 256
#define MEM_CAP 8192
#define CODE_CAP 4096
#define CD_CAP 4096
#define SLOTS 1024
#define STEP_CAP 1000000

typedef uint64_t u256[4]; /* little-endian limbs: w[0] is lowest */

static u256 evm_stack[STACK_CAP];
static u256 evm_storage[SLOTS];
static u256 storage_snapshot[SLOTS];
static uint8_t evm_mem[MEM_CAP];
static uint8_t code_buf[CODE_CAP];
static uint8_t cd_buf[CD_CAP];
static uint8_t jumpdests[CODE_CAP];

static const uint8_t ERC20_RUNTIME[75] = {
    0x60, 0x04, 0x35, 0x60, 0x00, 0x52, 0x60, 0x24, 0x35, 0x60, 0x20, 0x52, 0x60, 0x44, 0x35, 0x60,
    0x40, 0x52, 0x60, 0x40, 0x51, 0x60, 0x00, 0x51, 0x54, 0x10, 0x61, 0x00, 0x40, 0x57, 0x60, 0x40,
    0x51, 0x60, 0x00, 0x51, 0x54, 0x03, 0x60, 0x00, 0x51, 0x55, 0x60, 0x40, 0x51, 0x60, 0x20, 0x51,
    0x54, 0x01, 0x60, 0x20, 0x51, 0x55, 0x60, 0x01, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3,
    0x5b, 0x60, 0x00, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3};

static void cpy256(u256 d, const u256 s) { for (int i = 0; i < 4; i++) d[i] = s[i]; }
static void zero256(u256 d) { for (int i = 0; i < 4; i++) d[i] = 0; }
static int is_zero256(const u256 a) { return (a[0] | a[1] | a[2] | a[3]) == 0; }
static void set_u64(u256 d, uint64_t v) { d[0] = v; d[1] = d[2] = d[3] = 0; }

/* -1 / 0 / +1 for a < b / a == b / a > b (unsigned). */
static int cmp256(const u256 a, const u256 b) {
    for (int i = 3; i >= 0; i--) {
        if (a[i] < b[i]) return -1;
        if (a[i] > b[i]) return 1;
    }
    return 0;
}

static void add256(u256 r, const u256 a, const u256 b) {
    uint64_t t[4], carry = 0;
    for (int i = 0; i < 4; i++) {
        uint64_t s1 = a[i] + carry;
        uint64_t c1 = s1 < a[i];
        uint64_t s = s1 + b[i];
        carry = c1 + (s < s1);
        t[i] = s;
    }
    cpy256(r, t);
}

static void sub256(u256 r, const u256 a, const u256 b) {
    uint64_t t[4], borrow = 0;
    for (int i = 0; i < 4; i++) {
        uint64_t s1 = a[i] - borrow;
        uint64_t b1 = s1 > a[i];
        uint64_t s = s1 - b[i];
        borrow = b1 + (s > s1);
        t[i] = s;
    }
    cpy256(r, t);
}

/* 32x32 -> 64 shift-and-add: the C `*` operator is unavailable (RV64I). */
static uint64_t mul32(uint32_t a, uint32_t b) {
    uint64_t r = 0, aa = a;
    for (int k = 0; k < 32; k++) if ((b >> k) & 1) r += aa << k;
    return r;
}

static void mul256(u256 r, const u256 a, const u256 b) {
    uint32_t ah[8], bh[8], rh[8];
    for (int i = 0; i < 4; i++) {
        ah[i << 1] = (uint32_t)a[i]; ah[(i << 1) + 1] = (uint32_t)(a[i] >> 32);
        bh[i << 1] = (uint32_t)b[i]; bh[(i << 1) + 1] = (uint32_t)(b[i] >> 32);
    }
    for (int i = 0; i < 8; i++) rh[i] = 0;
    for (int i = 0; i < 8; i++) {
        uint64_t carry = 0;
        for (int j = 0; j + i < 8; j++) {
            uint64_t t = rh[i + j] + mul32(ah[i], bh[j]) + carry;
            rh[i + j] = (uint32_t)t;
            carry = t >> 32;
        }
    }
    uint64_t t[4];
    for (int i = 0; i < 4; i++) t[i] = rh[i << 1] | ((uint64_t)rh[(i << 1) + 1] << 32);
    cpy256(r, t);
}

/* shift < 256 (caller checks). */
static void shl256(u256 r, const u256 a, uint64_t shift) {
    uint64_t t[4];
    int word = (int)(shift >> 6);
    unsigned bit = (unsigned)(shift & 63);
    for (int i = 0; i < 4; i++) t[i] = 0;
    for (int i = 3; i >= 0; i--) {
        int src = i - word;
        if (src < 0) continue;
        uint64_t v = bit ? (a[src] << bit) : a[src];
        if (bit && src > 0) v |= a[src - 1] >> (64 - bit);
        t[i] = v;
    }
    cpy256(r, t);
}

static void shr256(u256 r, const u256 a, uint64_t shift) {
    uint64_t t[4];
    int word = (int)(shift >> 6);
    unsigned bit = (unsigned)(shift & 63);
    for (int i = 0; i < 4; i++) t[i] = 0;
    for (int i = 0; i < 4; i++) {
        int src = i + word;
        if (src > 3) continue;
        uint64_t v = bit ? (a[src] >> bit) : a[src];
        if (bit && src < 3) v |= a[src + 1] << (64 - bit);
        t[i] = v;
    }
    cpy256(r, t);
}

static void from_be(u256 r, const uint8_t *p) {
    for (int i = 0; i < 4; i++) {
        uint64_t v = 0;
        for (int j = 0; j < 8; j++) v = (v << 8) | p[j];
        r[3 - i] = v;
        p += 8;
    }
}

static void to_be(uint8_t *p, const u256 a) {
    for (int i = 0; i < 4; i++) {
        uint64_t v = a[3 - i];
        for (int j = 7; j >= 0; j--) { p[j] = (uint8_t)v; v >>= 8; }
        p += 8;
    }
}

/* Interpreter state. halt: 0 running, 1 STOP/RETURN, 2 REVERT, 3 error. */
static int sp, halt;
static uint64_t code_len, cd_len, ret_off, ret_len;

static int push(const u256 v) {
    if (sp >= STACK_CAP) { halt = 3; return 0; }
    cpy256(evm_stack[sp++], v);
    return 1;
}
static int pop(u256 v) {
    if (sp <= 0) { halt = 3; return 0; }
    cpy256(v, evm_stack[--sp]);
    return 1;
}
/* Small-value view: returns low limb if the rest is zero, else ~0. */
static uint64_t as_u64(const u256 a) {
    return (a[1] | a[2] | a[3]) ? ~(uint64_t)0 : a[0];
}

static void run(void) {
    uint64_t pc = 0, steps = 0;
    u256 a, b, r;
    while (!halt) {
        if (pc >= code_len) { halt = 1; break; } /* implicit STOP */
        if (++steps > STEP_CAP) { halt = 3; break; }
        uint8_t op = code_buf[pc++];
        if (op >= 0x60 && op <= 0x7F) { /* PUSH1..32 */
            int nb = op - 0x5F;
            zero256(r);
            for (int i = 0; i < nb; i++) {
                uint8_t byte = (pc + (uint64_t)i < code_len) ? code_buf[pc + i] : 0;
                int bitpos = (nb - 1 - i) << 3;
                r[bitpos >> 6] |= (uint64_t)byte << (bitpos & 63);
            }
            pc += (uint64_t)nb;
            push(r);
        } else if (op >= 0x80 && op <= 0x83) { /* DUP1..4 */
            int n = op - 0x7F;
            if (sp < n) { halt = 3; break; }
            push(evm_stack[sp - n]);
        } else if (op >= 0x90 && op <= 0x91) { /* SWAP1..2 */
            int n = op - 0x8F;
            if (sp < n + 1) { halt = 3; break; }
            cpy256(a, evm_stack[sp - 1]);
            cpy256(evm_stack[sp - 1], evm_stack[sp - 1 - n]);
            cpy256(evm_stack[sp - 1 - n], a);
        } else switch (op) {
        case 0x00: halt = 1; break; /* STOP */
        case 0x01: case 0x02: case 0x03: case 0x10: case 0x11: case 0x14:
        case 0x16: case 0x17: case 0x18: case 0x1B: case 0x1C:
            if (!pop(a) || !pop(b)) break; /* a = top, b = second */
            if (op == 0x01) add256(r, a, b);
            else if (op == 0x02) mul256(r, a, b);
            else if (op == 0x03) sub256(r, a, b);
            else if (op == 0x10) set_u64(r, cmp256(a, b) < 0);
            else if (op == 0x11) set_u64(r, cmp256(a, b) > 0);
            else if (op == 0x14) set_u64(r, cmp256(a, b) == 0);
            else if (op == 0x16) { for (int i = 0; i < 4; i++) r[i] = a[i] & b[i]; }
            else if (op == 0x17) { for (int i = 0; i < 4; i++) r[i] = a[i] | b[i]; }
            else if (op == 0x18) { for (int i = 0; i < 4; i++) r[i] = a[i] ^ b[i]; }
            else { /* SHL/SHR: a = shift (top), b = value */
                uint64_t s = as_u64(a);
                if (s == ~(uint64_t)0 || s >= 256) zero256(r);
                else if (op == 0x1B) shl256(r, b, s);
                else shr256(r, b, s);
            }
            push(r);
            break;
        case 0x15: /* ISZERO */
            if (!pop(a)) break;
            set_u64(r, is_zero256(a));
            push(r);
            break;
        case 0x35: { /* CALLDATALOAD */
            if (!pop(a)) break;
            uint64_t off = as_u64(a);
            uint8_t word[32];
            for (int i = 0; i < 32; i++)
                word[i] = (off != ~(uint64_t)0 && off + (uint64_t)i < cd_len)
                              ? cd_buf[off + i] : 0;
            from_be(r, word);
            push(r);
            break;
        }
        case 0x36: /* CALLDATASIZE */
            set_u64(r, cd_len);
            push(r);
            break;
        case 0x51: { /* MLOAD */
            if (!pop(a)) break;
            uint64_t off = as_u64(a);
            if (off == ~(uint64_t)0 || off + 32 > MEM_CAP) { halt = 3; break; }
            from_be(r, evm_mem + off);
            push(r);
            break;
        }
        case 0x52: { /* MSTORE: offset (top), value */
            if (!pop(a) || !pop(b)) break;
            uint64_t off = as_u64(a);
            if (off == ~(uint64_t)0 || off + 32 > MEM_CAP) { halt = 3; break; }
            to_be(evm_mem + off, b);
            break;
        }
        case 0x54: /* SLOAD: slot = low 64 bits of key */
            if (!pop(a)) break;
            if (a[0] >= SLOTS) { halt = 3; break; }
            push(evm_storage[a[0]]);
            break;
        case 0x55: /* SSTORE: key (top), value */
            if (!pop(a) || !pop(b)) break;
            if (a[0] >= SLOTS) { halt = 3; break; }
            cpy256(evm_storage[a[0]], b);
            break;
        case 0x56: case 0x57: { /* JUMP / JUMPI */
            if (!pop(a)) break;
            uint64_t dest = as_u64(a), cond = 1;
            if (op == 0x57) {
                if (!pop(b)) break;
                cond = !is_zero256(b);
            }
            if (cond) {
                if (dest == ~(uint64_t)0 || dest >= code_len || !jumpdests[dest]) {
                    halt = 3; break;
                }
                pc = dest;
            }
            break;
        }
        case 0x5B: break; /* JUMPDEST */
        case 0xF3: case 0xFD: { /* RETURN / REVERT: offset (top), size */
            if (!pop(a) || !pop(b)) break;
            uint64_t off = as_u64(a), size = as_u64(b);
            if (size == ~(uint64_t)0 || (size && (off == ~(uint64_t)0 ||
                off + size > MEM_CAP))) { halt = 3; break; }
            ret_off = size ? off : 0;
            ret_len = size;
            halt = (op == 0xF3) ? 1 : 2;
            break;
        }
        default: halt = 3; break;
        }
    }
}

int main(void) {
    const uint8_t *in = om_input();
    uint64_t len = om_input_len(), off = 0;
    if (len < 8) return 1;
    uint64_t want_code = om_read_u64(0);
    off = 8;
    if (want_code == 0) {
        code_len = sizeof(ERC20_RUNTIME);
        for (uint64_t i = 0; i < code_len; i++) code_buf[i] = ERC20_RUNTIME[i];
    } else {
        if (want_code > CODE_CAP || off + want_code > len) return 1;
        code_len = want_code;
        for (uint64_t i = 0; i < code_len; i++) code_buf[i] = in[off + i];
        off += code_len;
    }
    if (off + 8 > len) return 1;
    cd_len = om_read_u64(off);
    off += 8;
    if (cd_len > CD_CAP || off + cd_len > len) return 1;
    for (uint64_t i = 0; i < cd_len; i++) cd_buf[i] = in[off + i];
    off += cd_len;
    if (off + 8 > len) return 1;
    uint64_t n_storage = om_read_u64(off);
    off += 8;
    if (n_storage > SLOTS) return 1;
    for (uint64_t i = 0; i < n_storage; i++) {
        if (off + 40 > len) return 1;
        uint64_t slot = om_read_u64(off);
        if (slot >= SLOTS) return 1;
        from_be(evm_storage[slot], in + off + 8);
        off += 40;
    }
    for (int i = 0; i < SLOTS; i++) cpy256(storage_snapshot[i], evm_storage[i]);

    /* Valid jump destinations: JUMPDEST bytes not inside PUSH data. */
    for (uint64_t pc = 0; pc < code_len;) {
        uint8_t op = code_buf[pc];
        if (op == 0x5B) jumpdests[pc] = 1;
        pc += (op >= 0x60 && op <= 0x7F) ? (uint64_t)(op - 0x5E) : 1;
    }

    sp = 0; halt = 0; ret_off = 0; ret_len = 0;
    run();
    uint64_t status = (halt == 1);
    if (!status)
        for (int i = 0; i < SLOTS; i++) cpy256(evm_storage[i], storage_snapshot[i]);

    om_write_u64(status);
    om_write_u64(halt == 3 ? 0 : ret_len);
    if (halt != 3 && ret_len) om_write(evm_mem + ret_off, (size_t)ret_len);
    uint64_t nz = 0;
    for (int i = 0; i < SLOTS; i++) if (!is_zero256(evm_storage[i])) nz++;
    om_write_u64(nz);
    uint8_t be[32];
    for (int i = 0; i < SLOTS; i++) {
        if (is_zero256(evm_storage[i])) continue;
        om_write_u64((uint64_t)i);
        to_be(be, evm_storage[i]);
        om_write(be, 32);
    }
    return 0;
}
