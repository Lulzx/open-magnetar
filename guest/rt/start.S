/* open-magnetar guest entry (informative tooling).
 * Initial register file is all zero (spec 09). RAM_BASE >= 2^31 cannot be formed
 * by lui+addi on RV64 (lui sign-extends), so all RAM addresses are pc-relative
 * (-mcmodel=medany); `la` below expands to auipc+addi. */
    .section .text.init, "ax"
    .globl _start
_start:
    la   sp, __stack_top
#ifdef OM_ZERO_BSS
    /* Not needed: RAM is zero-initialised by M_0. Costs cycles. */
    la   t0, __bss_start
    la   t1, __bss_end
1:  bgeu t0, t1, 2f
    sd   zero, 0(t0)
    addi t0, t0, 8
    j    1b
2:
#endif
    call main
    /* a0 = main's return value = exit code */
    li   a7, 0
    ecall
3:  j    3b
