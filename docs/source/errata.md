# Errata

## Back-To-Back Write Transactions Not Supported on AHB-Lite Bus

* **Description**:
The AHB-Lite bus interface for LSU is not optimized for write performance.
Each aligned store is issued to the bus as a single write transaction followed by an idle cycle.
Each unaligned store is issued to the bus as multiple backto-back byte write transactions followed by an idle cycle.
These idle cycles limit the achievable bus utilization for writes.
* **Symptoms**: Potential performance impact for writes with AHB-Lite bus.
* **Workaround**: None.

## Debug Abstract Command Register May Return Non-Zero Value On Read

* **Description**:
The RISC-V External Debug specification specifies the abstract command (`command`) register as write-only (see Section 3.14.7 in [[3]](intro.md#ref-3)).
However, the VeeR EL2 implementation supports write as well as read operations to this register.
This may help a debugger's feature discovery process, but is not fully compliant with the RISC-V External Debug specification.
Because the expected return value for reading this register is always zero, it is unlikely that a debugger expecting a zero value would attempt to read it.
* **Symptoms**: Reading the debug abstract command (`command`) register may return a non-zero value.
* **Workaround**: A debugger should avoid reading the abstract command register if it cannot handle non-zero data.
