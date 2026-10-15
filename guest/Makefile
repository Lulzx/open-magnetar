# Verified toolchain (macOS/Homebrew): LLVM clang + lld.
#   brew install llvm lld
#   PATH=/opt/homebrew/opt/llvm/bin:/opt/homebrew/opt/lld/bin:$PATH make -C guest
# CC is overridable on the command line; -fuse-ld=lld needs ld.lld on PATH.
# I/O region sizes default to I=14 O=14 (128 KiB each) so every example,
# including the large-output ones (radix-sort, lz4, varint), fits one
# uniform Params(ram=20, input=14, output=14) host configuration.
A ?= 20
I ?= 14
O ?= 14
STACK_SIZE ?= 65536
M := $(shell echo $$(( $(I) > $(O) ? $(I) : $(O) )))
IN_BASE_WORD  := $(shell echo $$(( (1 << $(A)) - (1 << ($(M)+1)) )))
OUT_BASE_WORD := $(shell echo $$(( $(IN_BASE_WORD) + (1 << $(M)) )))
RAM_BASE := 2147483648
ifeq ($(origin CC),default)
CC := /opt/homebrew/opt/llvm/bin/clang
endif
CFLAGS := --target=riscv64 -march=rv64i -mabi=lp64 -mcmodel=medany -mno-relax -O2 \
          -nostdlib -ffreestanding -fno-pic -fno-builtin -I.
LDFLAGS := -fuse-ld=lld -nostdlib -static -Wl,-T,link.ld -Wl,-z,max-page-size=8 \
  -Wl,--defsym=__stack_top=$(shell echo $$(( $(RAM_BASE) + 8*$(IN_BASE_WORD) ))) \
  -Wl,--defsym=__input_base=$(shell echo $$(( $(RAM_BASE) + 8*$(IN_BASE_WORD) ))) \
  -Wl,--defsym=__output_base=$(shell echo $$(( $(RAM_BASE) + 8*$(OUT_BASE_WORD) ))) \
  -Wl,--defsym=__stack_size=$(STACK_SIZE)

all: $(patsubst %.c,%.elf,$(wildcard examples/*.c))
%.elf: %.c rt/start.S rt/om.h link.ld
	$(CC) $(CFLAGS) $(LDFLAGS) rt/start.S $< -o $@
clean:
	rm -f examples/*.elf
