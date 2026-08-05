### Formal testbench for 64-bit RVECC Encoder and Decoder

This is a comprehensive Formal testbench that verifies detection of all possible single-bit and double-bit errors. It has a short runtime of under 4 minutes thanks to aggressive Formal proof runtime optimization techniques. 

### Run Command:
```
ebmc --z3 --k-induction --bound 1 --systemverilog --top rvecc_sva rvecc_sva.sv top.sv channel_model.sv beh_lib.sv
``` 

### Tool used: 
HW-CBMC model checker https://github.com/diffblue/hw-cbmc

