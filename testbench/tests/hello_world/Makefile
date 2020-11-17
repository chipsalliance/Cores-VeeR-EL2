export TEST = hello_world
export OFILES = crt0.o hello_world.o
export BUILD_PATH = $(shell pwd)/snapshots/default

program.hex:
	$(MAKE) -e -f $(RV_ROOT)/tools/make.common $(BUILD_PATH)/defines.h
	$(MAKE) -e -f $(RV_ROOT)/tools/make.common $@

.DEFAULT:
	$(MAKE) -e program.hex
	$(MAKE) -e -f $(RV_ROOT)/tools/make.common $@
