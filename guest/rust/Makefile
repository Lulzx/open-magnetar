# Build Rust guests for open-magnetar (spec 14.5).
#
#   make -C guest/rust              # builds examples/fib (A=16, I=O=14)
#   make -C guest/rust A=20         # match another verifying key
#
# The canonical toolchain is nightly (for -Zbuild-std). With a stable
# toolchain that has the rust-src component, BOOTSTRAP=1 also works:
#
#   make -C guest/rust BOOTSTRAP=1
#
# The A/I/O values must match the ones passed to `om keygen`, exactly as
# with the C guests (see guest/Makefile). The resulting ELF is copied to
# examples/<name>.elf, next to the C guests.
A ?= 16
I ?= 14
O ?= 14
STACK_SIZE ?= 65536

M := $(shell echo $$(( $(I) > $(O) ? $(I) : $(O) )))
IN_BASE_WORD  := $(shell echo $$(( (1 << $(A)) - (1 << ($(M)+1)) )))
OUT_BASE_WORD := $(shell echo $$(( $(IN_BASE_WORD) + (1 << $(M)) )))
RAM_BASE := 2147483648
STACK_TOP := $(shell echo $$(( $(RAM_BASE) + 8*$(IN_BASE_WORD) )))
INPUT_BASE := $(STACK_TOP)
OUTPUT_BASE := $(shell echo $$(( $(RAM_BASE) + 8*$(OUT_BASE_WORD) )))

DEFSYMS := __stack_top=$(STACK_TOP) __input_base=$(INPUT_BASE) __output_base=$(OUTPUT_BASE) __stack_size=$(STACK_SIZE)
LINK_ARGS = -C link-arg=-T -C link-arg=$(ROOT)/guest/link.ld $(foreach s,$(DEFSYMS),-C link-arg=--defsym=$(s))

ifeq ($(BOOTSTRAP),1)
CARGO_BUILD := RUSTC_BOOTSTRAP=1 cargo build
else
CARGO_BUILD := cargo +nightly build
endif

ROOT := $(abspath ../..)
TARGET_JSON := guest/rust/riscv64i-open-magnetar-none-elf.json
TARGET_DIR := $(ROOT)/target/rust-guest

.PHONY: all fib clean
all: fib

fib:
	cd $(ROOT) && RUSTFLAGS="$(LINK_ARGS)" $(CARGO_BUILD) --release \
	  -p om-guest-fib --manifest-path guest/rust/Cargo.toml \
	  --target $(TARGET_JSON) --target-dir $(TARGET_DIR) \
	  -Zjson-target-spec -Zbuild-std=core,alloc,compiler_builtins \
	  -Zbuild-std-features=compiler-builtins-mem
	cp $(TARGET_DIR)/riscv64i-open-magnetar-none-elf/release/om-guest-fib examples/fib-rust.elf

clean:
	rm -rf $(TARGET_DIR) examples/fib-rust.elf
