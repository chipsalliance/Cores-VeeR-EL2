# Release notes

## 2.0

* Extended the core with support for RISC-V User privilege level
* Extended the core with support for PMP and ePMP functionalities
* ICache memory is now exported from the main core and can be provided at SoC integration level
* Many smaller changes and bugfixes
* Extended the repository with an array of tests and CI covering various core configurations

## 1.4

* Upgraded bit-manipulation support for Zba, Zbb, Zbc, Zbe, Zbf, Zbp, Zbr, Zbs to `0.94` draft spec.
  * Zba, Zbb, Zbc and Zbs are enabled by default. Use `-set=bitmanip_zb*=1` to enable other sub-extensions.
* Simulation performance improvement coding style changes in branch predictor and PIC
* Several corner case and exotic bug fixes :
  * MPC run ack timing
  * Force halt mechanism and MPC
  * Store data collision with DCCM DMA error when address is 0x0
  * RAW hazard on mtdata1
  * Errors on DMA access could leak into Dbg abstract cmd ocurring at same time
  * Icache parity error and branch error collision leading to fwd progress issue
* Fixed linter warning for async reset
 

## 1.3

* Multiple debug module compliance deviations and bugs reported by Codasip
* Updates to debug module to level compliance to version 0.13.2 of debug spec
* Trigger chaining compliance fixes
* Power optimization improvements and clock gating improvements
  * Significantly lower power in sleep as well as normal operation.
* Enhanced debug memory abstract command to access internal as well as external memories
* Added bit-manipulation support for Zba, Zbb, Zbc, Zbe, Zbf, Zbp, Zbr, Zbs (Jan 29, 2020 Draft spec).
  * Zbs and Zbb are enabled by default. Use `-set=bitmanip_zb*=1` to enable other sub-extensions.
* Enhancements and additional configurations options for a faster divider
* JTAG bypass register intial state issue fixed
* New branch predictor fully-associative option with 8,16,32 entries.
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
  * Generating link.ld with veer.config
    
## 1.2

* Modified MSCAUSE encoding to be consistent with current internal specification
* Added internal timers

## 1.1

* Several bug fixes in debug module
  * Added new `dbg_rst_l` input for system wide reset to debug module. If debug module operation during core reset is not needed, this can be connected to `rst_l`.
* Trace port width adjusted
* Demo testbench has a synthesizable bridge to allow accessing the ICCM with load/stores via the DMA port. (*This only works with the AXI4 build*)

## 1.0

Initial release
