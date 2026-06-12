GCC_PREFIX    ?= riscv64-unknown-elf
MAKEFILE_PATH  = $(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
PICOLIBC_PATH  = $(abspath $(MAKEFILE_PATH)/../third_party/picolibc)
BUILD_PATH     = $(PICOLIBC_PATH)/build
INSTALL_PATH   = $(PICOLIBC_PATH)/install

ifeq ($(CCACHE), )
	MESON_CROSS_CC = '$(GCC_PREFIX)-gcc'
else
	MESON_CROSS_CC = ['$(CCACHE)', '$(GCC_PREFIX)-gcc']
endif

define CROSSFILE
[binaries]
c     = $(MESON_CROSS_CC)
ar    = '$(GCC_PREFIX)-gcc-ar'
as    = '$(GCC_PREFIX)-as'
nm    = '$(GCC_PREFIX)-gcc-nm'
strip = '$(GCC_PREFIX)-strip'

[host_machine]
system     = 'unknown'
cpu_family = 'riscv64'
cpu        = 'riscv'
endian     = 'little'

[properties]
# this uses shorter but slower function entry code
c_args = [ '-msave-restore' ]
# default multilib is 64 bit
c_args_ = [ '-mcmodel=medany' ]
endef

export CROSSFILE

$(BUILD_PATH):
	mkdir -p $@

$(BUILD_PATH)/cross.txt: | $(BUILD_PATH)
	@echo "$$CROSSFILE" > $@

$(INSTALL_PATH)/picolibc.specs: $(BUILD_PATH)/cross.txt | $(BUILD_PATH)

	cd $(PICOLIBC_PATH) && meson $(BUILD_PATH) \
		-Dmultilib=true \
		-Dmultilib-list=rv32imac/ilp32 \
		-Dpicocrt=false \
		-Datomic-ungetc=false \
		-Dthread-local-storage=false \
		-Dio-long-long=true \
		-Dformat-default=integer \
		-Dincludedir=picolibc/$(GCC_PREFIX)/include \
		-Dlibdir=picolibc/$(GCC_PREFIX)/lib \
        -Dprefix=$(INSTALL_PATH) \
        -Dspecsdir=$(INSTALL_PATH) \
		--cross-file $(BUILD_PATH)/cross.txt

	cd $(BUILD_PATH) && meson install

all: $(INSTALL_PATH)/picolibc.specs

clean:
	rm -rf $(BUILD_PATH)

.PHONY: all clean
