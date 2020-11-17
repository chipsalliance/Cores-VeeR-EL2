export TEST = cmark
#export CONF_PARAMS= -set=btb_size=512 -set=bht_size=2048 -set=iccm_size=128
export CONF_PARAMS= -set=btb_size=512 -set=bht_size=2048 -set=iccm_enable=0
export OFILES = crt0.o cmark.o printf.o 
export BUILD_PATH = $(shell pwd)/snapshots/default
export TEST_CFLAGS = -finline-limit=400 -mbranch-cost=1 -Ofast -fno-code-hoisting -funroll-all-loops

program.hex:
	$(MAKE) -e -f $(RV_ROOT)/tools/make.common $(BUILD_PATH)/defines.h
	$(MAKE) -e -f $(RV_ROOT)/tools/make.common $@

.DEFAULT:
	$(MAKE) -e program.hex
	$(MAKE) -e -f $(RV_ROOT)/tools/make.common $@
