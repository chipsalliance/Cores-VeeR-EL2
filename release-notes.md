# EL2 SweRV RISC-V Core<sup>TM</sup> 1.3 from Western Digital


* Multiple debug module compliance deviations and bugs reported by Codasip
* Updates to debug module to level compliance to version 0.13.2 of debug spec
* Trigger chaining compliance fixes
* Power optimization improvements and clock gating improvements
    * Significantly lower power in sleep as well as normal operation.
* Enhanced debug memory abstract command to access internal as well as external memories
* Added bit-manipulation support for Zba, Zbb, Zbc, Zbe, Zbf, Zbp, Zbr, Zbs (Jan 29, 2020 Draft spec).
    * Zbs and Zbb are enabled by default. Use -set=bitmanip+zb*=1 to enable other sub-extensions.
* Enhancements and additional configurations options for a faster divider
* JTAG controller intial state issue fixed
* Branch predictor fully-associative mode for 8,16,32 entries.
* Corner case bugs fixes related to 
    * Bus protocol corner cases (ahb)
    * Fetch bus error recording improved accuracy
    * Branch predictor pathological timing cases fixes
    * Fast interrupt with DCCM ECC errors priority bug
    * MPC & PMU protocol cleanup
    * Performance counter bug fixes (counting branch prediction events)
    * Triggers and ECC correctable error overflows bug fixes

* Demo test-bench updates
    * Handling bigger test sizes using associative arrays in external memory slaves, 
    * simplified test building process and CCM loading functions (only program.hex is generated, no data.hex)
    * Improved Makefile and example tests (see README)
    * Generating crt0 and link.ld from swerv.config
    
# EL2 SweRV RISC-V Core<sup>TM</sup> 1.2 from Western Digital
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
