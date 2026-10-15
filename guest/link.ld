/* open-magnetar guest linker script (informative tooling; see spec 14 section 14.5).
 * Required symbols, passed by the Makefile with --defsym:
 *   __stack_top   byte address of the initial sp (RAM_BASE + 8*in_base_word)
 *   __input_base  byte address of the input region
 *   __output_base byte address of the output region
 *   __stack_size  bytes reserved for the stack (heap ends below it)
 */
ENTRY(_start)
CODE_BASE = 0x10000000;
RAM_BASE  = 0x80000000;
PHDRS {
  text PT_LOAD FLAGS(5);   /* R+X */
  data PT_LOAD FLAGS(6);   /* R+W */
}
SECTIONS {
  . = CODE_BASE;
  .text : { KEEP(*(.text.init)) *(.text .text.*) } :text
  . = RAM_BASE;
  .rodata : ALIGN(8) { *(.rodata .rodata.* .srodata .srodata.*) } :data
  .data   : ALIGN(8) { *(.data .data.* .sdata .sdata.*) } :data
  .bss    : ALIGN(8) { __bss_start = .; *(.sbss .sbss.* .bss .bss.* COMMON) . = ALIGN(8); __bss_end = .; } :data
  __heap_start = .;
  __heap_end = __stack_top - __stack_size;
  /DISCARD/ : { *(.comment) *(.eh_frame*) *(.riscv.attributes) *(.note*) }
}
