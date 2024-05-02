# Machine to/from user mode switching tests

The test is intended to verify switching of operating privilege mode. This includes checking `mcause` values for exceptions and behavior of `mstatus.MPP` and `mstatus.MPRV` fields.

Flow of the test:

- Core resets to M mode. Check if `MPRV` is cleared and `MPP` indicated machine mode (2'b11).

- Returning from an exception via `mret` should set `MPP` to the least privileged mode and not affect `MPRV` when returning to M mode. Do the following:

    - Clear `MPRV` and do an `ECALL`. This should trigger an exception with `mcause=0xb`. Returning from an exception via `mret` should set `MPP` to the least privileged mode. Check if `MPRV` is cleared and `MPP` equals `2'b00` after returning.

    - Set `MPRV` and do an `ECALL` again. This should trigger an exception with `mcause=0xb`. Returning from an exception via `mret` to M mode should not affect `MPRV`. Check if `MPRV` is set and `MPP` equals `2'b00` after returning.

- Go to user mode by clearing `MPRV` and `MPP` followed by issuing `mret`.

- CSRs are not accessible from U mode. Therefore the test implements a "syscall" mechanism via `ECALL`. The mechanism allows passing one argument to and a single return value from a "syscall" call. When returning from an exception via `mret` to U mode `MPP` should behave the same (set to the least privilege mode) but `MPRV` should be cleared. To test that:

    - Issue `ECALL_CLR_MPRV` syscall. This should trigger an exception with `mcause=0x8`, clear `MPRV` and return the last written value to `mstatus`. Check if `MPP` of the returned CSR value is set to `2'b00`.
    
    - Issue `ECALL_SET_MPRV` syscall. This should trigger the same exception as above, set `MPRV` and return the value written to `mstatus`. Since we are returning to U mode `MPRV` should be cleared during `mret`. Check if `MPP` of the returned CSR value is set to `2'b00` as well.
    
    - To check if indeed the previous `mret` cleared `MPRV` issue `ECALL_GET_MSTATUS` syscall which just returns the captured `mstatus` CSR value. Check if `MPRV` is cleared there.
    
- Finally verify the sequence of traps taken by comparing recorded `mcause` and `mstatus` values against a golden reference.

