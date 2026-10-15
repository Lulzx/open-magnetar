# Informative tooling; UNTESTED (no riscv-capable clang/lld was available when written).
A ?= 20
I ?= 12
O ?= 8
STACK_SIZE ?= 65536
M := $(shell echo $$(( $(I) > $(O) ? $(I) : $(O) )))
IN_BASE_WORD  := $(shell echo $$(( (1 << $(A)) - (1 << ($(M)+1)) )))
OUT_BASE_WORD := $(shell echo $$(( $(IN_BASE_WORD) + (1 << $(M)) )))
RAM_BASE := 2147483648
CC := clang
CFLAGS := --target=riscv64 -march=rv64i -mabi=lp64 -mcmodel=medany -mno-relax -O2 \
          -nostdlib -ffreestanding -fno-pic -fno-builtin -I.
LDFLAGS := -fuse-ld=lld -nostdlib -static -Wl,-T,link.ld -Wl,-z,max-page-size=8 \
  -Wl,--defsym=__stack_top=$(shell echo $$(( $(RAM_BASE) + 8*$(IN_BASE_WORD) ))) \
  -Wl,--defsym=__input_base=$(shell echo $$(( $(RAM_BASE) + 8*$(IN_BASE_WORD) ))) \
  -Wl,--defsym=__output_base=$(shell echo $$(( $(RAM_BASE) + 8*$(OUT_BASE_WORD) ))) \
  -Wl,--defsym=__stack_size=$(STACK_SIZE)

all: examples/fib.elf
%.elf: %.c rt/start.S rt/om.h link.ld
	$(CC) $(CFLAGS) $(LDFLAGS) rt/start.S $< -o $@
clean:
	rm -f examples/*.elf
