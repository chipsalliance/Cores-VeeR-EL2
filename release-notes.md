# EL2 SweRV RISC-V Core<sup>TM</sup> 1.2 from Western Digital

## Release Notes

## Release Notes

* Modified MSCAUSE encoding to be consistent with current internal specification
* Added internal timers


# EL2 SweRV RISC-V Core<sup>TM</sup> 1.1 from Western Digital

## Release Notes

* Several bug fixes in debug module
    * Added new `dbg_rst_l` input for system wide reset to debug module. If debug module operation during core reset is not needed, this can be connected to `rst_l`.
* Trace port width adjusted
* Demo testbench has a synthesizable bridge to allow accessing the ICCM with load/stores via the DMA port. (*This only works with the AXI4 build*)

# EL2 SweRV RISC-V Core<sup>TM</sup> 1.0 from Western Digital

## Release Notes

Initial release
