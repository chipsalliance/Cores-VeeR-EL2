# VeeR EL2 RISC-V Core

## Configuration

### Contents
Name                    | Description
----------------------  | ------------------------------
VeeR.config             | Configuration script for VeeR-EL2
veer_config_gen.py      | Python wrapper to run veer.config, used by VeeRVolf


This script will generate a consistent set of `defines/#defines/parameters` needed for the design and testbench.
A perl hash (*perl_configs.pl*) and a JSON format for VeeR-iss are also generated.
This set of include files :

    ./snapshots/<target>
    ├── common_defines.vh                       # `defines for testbench
    ├── defines.h                               # #defines for C/assembly headers
    ├── el2_param.vh                            # Actual Design parameters
    ├── el2_pdef.vh                             # Parameter structure definition
    ├── pd_defines.vh                           # `defines for physical design
    ├── perl_configs.pl                         # Perl %configs hash for scripting
    ├── pic_map_auto.h                          # PIC memory map based on configure size
    ├── whisper.json                            # JSON file for veer-iss
    └── link.ld                                 # Default linker file for tests



While the defines may be modified by hand, it is recommended that this script be used to generate a consistent set.

### Targets
There are 4 predefined target configurations: `default`, `default_ahb`, `typical_pd` and `high_perf` that can be selected via the `-target=name` option to veer.config.

Target                  | Description
----------------------  | ------------------------------
default                 | Default configuration. AXI4 bus interface
default_ahb             | Default configuration, AHB-Lite bus interface
typical_pd              | No ICCM, AXI4 bus interface
high_perf               | Large BTB/BHT, AXI4 interface


`veer.config` may be edited to add additional target configurations, or new configurations may be created via the command line `-set` or `-unset` options.

**Run `$RV_ROOT/configs/veer.config -h` for options and settable parameters.**
