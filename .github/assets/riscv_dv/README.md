# RISCV-DV tests

This folder contains pre-generated RISCV-DV test programs for VeeR. Normally the programs are generated and cached by the CI using proprietary tools. In case of a failure during this process the CI falls back to the code stored in this folder.

The programs were generated using RISCV-DV SHA [f01f628](https://github.com/chipsalliance/riscv-dv/commit/f01f62867adaa23c24d84374b8183e7c92116958) and veer-el2 SHA [97ffac3](https://github.com/chipsalliance/Cores-VeeR-EL2/commit/97ffac34a3fd957a85f76daca6ac31443c4552a1) with the following command:
```
pushd tools/riscv-dv
  make -j`nproc` \
    RISCV_DV_TEST=$RISCV_DV_TEST
    RISCV_DV_ITER=3
    RISCV_DV_SEED=999
    generate
popd
```

Test names used are defined in `target/rv32imc/testlist.yaml` in RISCV-DV repository.
