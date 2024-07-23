*** Keywords ***
Prepare Machine
    [Arguments]                     ${bin}
    Execute Command                 $bin=@${bin}
    Execute Command                 i @${CURDIR}/veer.resc
    Create Terminal Tester          sysbus.htif  timeout=0  defaultMatchNextLine=true
    Create Log Tester               1
    Execute Command                 logLevel 0 sysbus.htif
    Wait For Log Entry              TEST FINISHED  level=Debug

Wait For Regex
    [Arguments]                     ${pattern}
    Wait For Line On Uart           ${pattern}  treatAsRegex=true

Wait For OK Message
    [Arguments]                     ${pattern}
    Wait For Regex                  \\[\\s+OK\\s+\\] ${pattern}

Check CSR Access
    [Arguments]                     ${pattern}  ${expect_trap}=${False}
    IF  ${expect_trap}
        Wait For Line On Uart       trap! mstatus=0x00000000, mcause=0x00000002
    END
    Wait For OK Message             ${pattern}

*** Test Cases ***
Should Have All CSRs
    Prepare Machine                 ${CURDIR}/csr_access.elf

    Wait For Line On Uart           ${EMPTY}
    Wait For Line On Uart           Hello VeeR
    Wait For Line On Uart           Testing CSR read...
    Check CSR Access                0xF11 'mvendorid'
    Check CSR Access                0xF12 'marchid'
    Check CSR Access                0xF13 'mimpid'
    Check CSR Access                0xF14 'mhartid'
    Check CSR Access                0x300 'mstatus'
    Check CSR Access                0x301 'misa'
    Check CSR Access                0x304 'mie'
    Check CSR Access                0x305 'mtvec'
    Check CSR Access                0x306 'mcounteren'
    Check CSR Access                0x320 'mcountinhibit'
    Check CSR Access                0x340 'mscratch'
    Check CSR Access                0x341 'mepc'
    Check CSR Access                0x342 'mcause'
    Check CSR Access                0x343 'mtval'
    Check CSR Access                0x344 'mip'
    Check CSR Access                0xB00 'mcycle'
    Check CSR Access                0xB02 'minstret'
    Check CSR Access                0xB80 'mcycleh'
    Check CSR Access                0xB82 'minstreth'
    Check CSR Access                0x30A 'menvcfg'
    Check CSR Access                0x31A 'menvcfgh'
    Check CSR Access                0x747 'mseccfg'
    Check CSR Access                0x757 'mseccfgh'
    Check CSR Access                0x3A0 'pmpcfg0'
    Check CSR Access                0x3B0 'pmpaddr0'
    Check CSR Access                0x3C0 'pmpaddr16'
    Check CSR Access                0x3D0 'pmpaddr32'
    Check CSR Access                0x3E0 'pmpaddr48'
    Check CSR Access                0xC00 'cycle'
    Check CSR Access                0xC80 'cycleh'
    Check CSR Access                0xC02 'instret'
    Check CSR Access                0xC82 'instreth'
    Check CSR Access                0x7FF 'mscause'
    Check CSR Access                0xBC0 'mdeau'
    Check CSR Access                0xFC0 'mdseac'
    Check CSR Access                0xBC8 'meivt'
    Check CSR Access                0xFC8 'meihap'
    Check CSR Access                0xBC9 'meipt'
    Check CSR Access                0xBCC 'meicurpl'
    Check CSR Access                0xBCB 'meicidpl'
    Check CSR Access                0x7A0 'mtsel'
    Check CSR Access                0x7A1 'mtdata1'
    Check CSR Access                0x7A2 'mtdata2'
    Check CSR Access                0x7C0 'mrac'
    Check CSR Access                0xB03 'mhpmc3'
    Check CSR Access                0xB04 'mhpmc4'
    Check CSR Access                0xB05 'mhpmc5'
    Check CSR Access                0xB06 'mhpmc6'
    Check CSR Access                0xB83 'mhpmc3h'
    Check CSR Access                0xB84 'mhpmc4h'
    Check CSR Access                0xB85 'mhpmc5h'
    Check CSR Access                0xB86 'mhpmc6h'
    Check CSR Access                0x323 'mhpme3'
    Check CSR Access                0x324 'mhpme4'
    Check CSR Access                0x325 'mhpme5'
    Check CSR Access                0x326 'mhpme6'
    Check CSR Access                0x7F0 'micect'
    Check CSR Access                0x7F1 'miccmect'
    Check CSR Access                0x7F2 'mdccmect'
    Check CSR Access                0x7C6 'mpmc'
    Check CSR Access                0x7F8 'mcgc'
    Check CSR Access                0x7C2 'mcpc'
    Check CSR Access                0x7F9 'mfdc'
    Check CSR Access                0x7D4 'mitctl0'
    Check CSR Access                0x7D7 'mitctl1'
    Check CSR Access                0x7D3 'mitb0'
    Check CSR Access                0x7D6 'mitb1'
    Check CSR Access                0x7D2 'mitcnt0'
    Check CSR Access                0x7D5 'mitcnt1'
    Check CSR Access                0xB07 'perfva'
    Check CSR Access                0xB08 'perfvb'
    Check CSR Access                0xB10 'perfvc'
    Check CSR Access                0xB87 'perfvd'
    Check CSR Access                0xB88 'perfve'
    Check CSR Access                0xB90 'perfvf'
    Check CSR Access                0x327 'perfvg'
    Check CSR Access                0x328 'perfvh'
    Check CSR Access                0x330 'perfvi'
    Check CSR Access                0x7CE 'mfdht'
    Check CSR Access                0x7CF 'mfdhs'
    Wait For Line On Uart           Testing CSR write...
    Check CSR Access                0x304 'mie'
    Check CSR Access                0x340 'mscratch'
    Check CSR Access                0x30A 'menvcfg'
    Check CSR Access                0x31A 'menvcfgh'
    Wait For Line On Uart           ${EMPTY}
    Wait For Line On Uart           Hello from user_main()
    Wait For Line On Uart           Testing CSR read...
    Check CSR Access                0xF11 'mvendorid'  expect_trap=${True}
    Check CSR Access                0xF12 'marchid'  expect_trap=${True}
    Check CSR Access                0xF13 'mimpid'  expect_trap=${True}
    Check CSR Access                0xF14 'mhartid'  expect_trap=${True}
    Check CSR Access                0x300 'mstatus'  expect_trap=${True}
    Check CSR Access                0x301 'misa'  expect_trap=${True}
    Check CSR Access                0x304 'mie'  expect_trap=${True}
    Check CSR Access                0x305 'mtvec'  expect_trap=${True}
    Check CSR Access                0x306 'mcounteren'  expect_trap=${True}
    Check CSR Access                0x320 'mcountinhibit'  expect_trap=${True}
    Check CSR Access                0x340 'mscratch'  expect_trap=${True}
    Check CSR Access                0x341 'mepc'  expect_trap=${True}
    Check CSR Access                0x342 'mcause'  expect_trap=${True}
    Check CSR Access                0x343 'mtval'  expect_trap=${True}
    Check CSR Access                0x344 'mip'  expect_trap=${True}
    Check CSR Access                0xB00 'mcycle'  expect_trap=${True}
    Check CSR Access                0xB02 'minstret'  expect_trap=${True}
    Check CSR Access                0xB80 'mcycleh'  expect_trap=${True}
    Check CSR Access                0xB82 'minstreth'  expect_trap=${True}
    Check CSR Access                0x30A 'menvcfg'  expect_trap=${True}
    Check CSR Access                0x31A 'menvcfgh'  expect_trap=${True}
    Check CSR Access                0x747 'mseccfg'  expect_trap=${True}
    Check CSR Access                0x757 'mseccfgh'  expect_trap=${True}
    Check CSR Access                0x3A0 'pmpcfg0'  expect_trap=${True}
    Check CSR Access                0x3B0 'pmpaddr0'  expect_trap=${True}
    Check CSR Access                0x3C0 'pmpaddr16'  expect_trap=${True}
    Check CSR Access                0x3D0 'pmpaddr32'  expect_trap=${True}
    Check CSR Access                0x3E0 'pmpaddr48'  expect_trap=${True}
    Check CSR Access                0xC00 'cycle'
    Check CSR Access                0xC80 'cycleh'
    Check CSR Access                0xC02 'instret'
    Check CSR Access                0xC82 'instreth'
    Check CSR Access                0x7FF 'mscause'  expect_trap=${True}
    Check CSR Access                0xBC0 'mdeau'  expect_trap=${True}
    Check CSR Access                0xFC0 'mdseac'  expect_trap=${True}
    Check CSR Access                0xBC8 'meivt'  expect_trap=${True}
    Check CSR Access                0xFC8 'meihap'  expect_trap=${True}
    Check CSR Access                0xBC9 'meipt'  expect_trap=${True}
    Check CSR Access                0xBCC 'meicurpl'  expect_trap=${True}
    Check CSR Access                0xBCB 'meicidpl'  expect_trap=${True}
    Check CSR Access                0x7A0 'mtsel'  expect_trap=${True}
    Check CSR Access                0x7A1 'mtdata1'  expect_trap=${True}
    Check CSR Access                0x7A2 'mtdata2'  expect_trap=${True}
    Check CSR Access                0x7C0 'mrac'  expect_trap=${True}
    Check CSR Access                0xB03 'mhpmc3'  expect_trap=${True}
    Check CSR Access                0xB04 'mhpmc4'  expect_trap=${True}
    Check CSR Access                0xB05 'mhpmc5'  expect_trap=${True}
    Check CSR Access                0xB06 'mhpmc6'  expect_trap=${True}
    Check CSR Access                0xB83 'mhpmc3h'  expect_trap=${True}
    Check CSR Access                0xB84 'mhpmc4h'  expect_trap=${True}
    Check CSR Access                0xB85 'mhpmc5h'  expect_trap=${True}
    Check CSR Access                0xB86 'mhpmc6h'  expect_trap=${True}
    Check CSR Access                0x323 'mhpme3'  expect_trap=${True}
    Check CSR Access                0x324 'mhpme4'  expect_trap=${True}
    Check CSR Access                0x325 'mhpme5'  expect_trap=${True}
    Check CSR Access                0x326 'mhpme6'  expect_trap=${True}
    Check CSR Access                0x7F0 'micect'  expect_trap=${True}
    Check CSR Access                0x7F1 'miccmect'  expect_trap=${True}
    Check CSR Access                0x7F2 'mdccmect'  expect_trap=${True}
    Check CSR Access                0x7C6 'mpmc'  expect_trap=${True}
    Check CSR Access                0x7F8 'mcgc'  expect_trap=${True}
    Check CSR Access                0x7C2 'mcpc'  expect_trap=${True}
    Check CSR Access                0x7F9 'mfdc'  expect_trap=${True}
    Check CSR Access                0x7D4 'mitctl0'  expect_trap=${True}
    Check CSR Access                0x7D7 'mitctl1'  expect_trap=${True}
    Check CSR Access                0x7D3 'mitb0'  expect_trap=${True}
    Check CSR Access                0x7D6 'mitb1'  expect_trap=${True}
    Check CSR Access                0x7D2 'mitcnt0'  expect_trap=${True}
    Check CSR Access                0x7D5 'mitcnt1'  expect_trap=${True}
    Check CSR Access                0xB07 'perfva'  expect_trap=${True}
    Check CSR Access                0xB08 'perfvb'  expect_trap=${True}
    Check CSR Access                0xB10 'perfvc'  expect_trap=${True}
    Check CSR Access                0xB87 'perfvd'  expect_trap=${True}
    Check CSR Access                0xB88 'perfve'  expect_trap=${True}
    Check CSR Access                0xB90 'perfvf'  expect_trap=${True}
    Check CSR Access                0x327 'perfvg'  expect_trap=${True}
    Check CSR Access                0x328 'perfvh'  expect_trap=${True}
    Check CSR Access                0x330 'perfvi'  expect_trap=${True}
    Check CSR Access                0x7CE 'mfdht'  expect_trap=${True}
    Check CSR Access                0x7CF 'mfdhs'  expect_trap=${True}
    Wait For Line On Uart           Testing CSR write...
    Check CSR Access                0x304 'mie'  expect_trap=${True}
    Check CSR Access                0x340 'mscratch'  expect_trap=${True}
    Check CSR Access                0x30A 'menvcfg'  expect_trap=${True}
    Check CSR Access                0x31A 'menvcfgh'  expect_trap=${True}
    Wait For Line On Uart           Attempting to write mscratch...
    Wait For Line On Uart           trap! mstatus=0x00000000, mcause=0x00000002
    Wait For Line On Uart           trap! mstatus=0x00000000, mcause=0x00000008
    Wait For Line On Uart           ${EMPTY}
    Wait For Line On Uart           Hello from machine_main()
    Wait For Line On Uart           Reading mscratch...
    Wait For Regex                  \\[\\s+OK\\s+\\]

    Wait For Line On Uart           Finished: PASSED  matchNextLine=false

Should Have Correct MStatus
    Prepare Machine                 ${CURDIR}/csr_mstatus.elf

    Wait For Line On Uart           M mode:
    Wait For Line On Uart           0x1800
    Wait For Line On Uart           0x1800
    Wait For Line On Uart           ok.
    Wait For Line On Uart           S mode:
    Wait For Line On Uart           0x800
    Wait For Line On Uart           0x0
    Wait For Line On Uart           not supported.
    Wait For Line On Uart           U mode:
    Wait For Line On Uart           0x0
    Wait For Line On Uart           0x0
    Wait For Line On Uart           ok.
    Wait For Line On Uart           MPRV
    Wait For Line On Uart           0x20000
    Wait For Line On Uart           0x20000
    Wait For Line On Uart           ok.
    Wait For Line On Uart           0x0
    Wait For Line On Uart           0x0
    Wait For Line On Uart           ok.

    Wait For Line On Uart           Finished: PASSED  matchNextLine=false

Should Have Correcr MISA
    Prepare Machine                 ${CURDIR}/csr_misa.elf

    Wait For Line On Uart           misa = 0x40101104 vs. 0x40101104
    Wait For Line On Uart           Finished: PASSED  matchNextLine=false

Should Pass Dhrystone Benchmark
    Prepare Machine                 ${CURDIR}/dhry.elf
    Wait For Line On Uart           Finished: PASSED  matchNextLine=false

Should Implement Insn
    Prepare Machine                 ${CURDIR}/insns.elf

    Wait For Line On Uart           Hello VeeR
    Wait For Line On Uart           testing EBREAK
    Wait For Line On Uart           trap! mstatus=0x1800, mcause=0x3, mepc=0x800002fa, insn=0x19002
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing ECALL
    Wait For Line On Uart           trap! mstatus=0x1800, mcause=0xb, mepc=0x80000332, insn=0x73
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing WFI
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing SRET
    Wait For Line On Uart           trap! mstatus=0x1800, mcause=0x2, mepc=0x80000378, insn=0x10200073
    Wait For Line On Uart           pass
    Wait For Line On Uart           Hello from user_main()
    Wait For Line On Uart           testing EBREAK
    Wait For Line On Uart           trap! mstatus=0x80, mcause=0x3, mepc=0x8000010c, insn=0x19002
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing ECALL
    Wait For Line On Uart           trap! mstatus=0x80, mcause=0x8, mepc=0x8000014c, insn=0x73
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing WFI
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing SRET
    Wait For Line On Uart           trap! mstatus=0x80, mcause=0x2, mepc=0x80000196, insn=0x10200073
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing MRET
    Wait For Line On Uart           trap! mstatus=0x80, mcause=0x2, mepc=0x800001c4, insn=0x30200073
    Wait For Line On Uart           pass

    Wait For Line On Uart           Finished: PASSED  matchNextLine=false

Should Correctly Implement Mode Switch
    Prepare machine                 ${CURDIR}/modesw.elf

    Wait For Line On Uart           Hello VeeR
    Wait For OK Message             MPRV cleared
    Wait For OK Message             MPP is 11
    Wait For Line On Uart           doing ECALL (MPRV=0)...
    Wait For Line On Uart           trap! mstatus=0x1800, mcause=0xb, mepc=0x80000136
    Wait For Line On Uart           Hello ECALL.M
    Wait For OK Message             MPRV cleared
    Wait For OK Message             MPP is 00
    Wait For Line On Uart           doing ECALL (MPRV=1)
    Wait For Line On Uart           trap! mstatus=0x21800, mcause=0xb, mepc=0x80000136
    Wait For Line On Uart           Hello ECALL.M
    Wait For OK Message             MPRV is set
    Wait For OK Message             MPP is 00
    Wait For Line On Uart           Hello from user_main()
    Wait For Line On Uart           doing ECALL...
    Wait For Line On Uart           trap! mstatus=0x80, mcause=0x8, mepc=0x80000136
    Wait For Line On Uart           Hello ECALL.U
    Wait For Line On Uart           clearing mstatus.MPRV
    Wait For OK Message             MPP is 00
    Wait For Line On Uart           doing ECALL...
    Wait For Line On Uart           trap! mstatus=0x80, mcause=0x8, mepc=0x80000136
    Wait For Line On Uart           Hello ECALL.U
    Wait For OK Message             MPRV was cleared
    Wait For Line On Uart           doing ECALL...
    Wait For Line On Uart           trap! mstatus=0x80, mcause=0x8, mepc=0x80000136
    Wait For Line On Uart           Hello ECALL.U
    Wait For Line On Uart           setting mstatus.MPRV
    Wait For OK Message             MPP is 00
    Wait For Line On Uart           doing ECALL...
    Wait For Line On Uart           trap! mstatus=0x80, mcause=0x8, mepc=0x80000136
    Wait For Line On Uart           Hello ECALL.U
    Wait For OK Message             MPRV was cleared
    Wait For Line On Uart           traps taken:
    Wait For Line On Uart           0. mcause=0xb mstatus=0x1800
    Wait For Line On Uart           1. mcause=0xb mstatus=0x21800
    Wait For Line On Uart           2. mcause=0x8 mstatus=0x80
    Wait For Line On Uart           3. mcause=0x8 mstatus=0x80
    Wait For Line On Uart           4. mcause=0x8 mstatus=0x80
    Wait For Line On Uart           5. mcause=0x8 mstatus=0x80
    Wait For OK Message             trap sequence verified

    Wait For Line On Uart           Finished: PASSED  matchNextLine=false

Should Implement PMP
    Prepare Machine                 ${CURDIR}/pmp.elf
    Wait For Line On Uart           Hello VeeR (M mode)
    Wait For Line On Uart           VeeR does not have Smepmp
    Wait For Line On Uart           PMP G=0, granularity is 4
    Wait For Line On Uart           00 - User mode RWX in default state
    Wait For Line On Uart           testing...
    Wait For Line On Uart           hello
    Wait For Line On Uart           pass
    Wait For Line On Uart           01 - User mode RWX with one (any) PMP region enabled
    Wait For Line On Uart           testing...
    Wait For Line On Uart           Trap! mcause=0x00000001, mepc=0x80000420, sp=0x80007E34
    Wait For Line On Uart           pass
    Wait For Line On Uart           02 - User mode RWX with code, data and stack access allowed
    Wait For Line On Uart           testing...
    Wait For Line On Uart           hello
    Wait For Line On Uart           pass
    Wait For Line On Uart           03 - User mode (MPRV=0, MPP=0) --- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           Trap! mcause=0x00000007, mepc=0x8000046C, sp=0x80007E24
    Wait For Line On Uart           data mismatch
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           Trap! mcause=0x00000005, mepc=0x800004DC, sp=0x80007DD4
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           Trap! mcause=0x00000001, mepc=0x80004040, sp=0x80007E34
    Wait For Line On Uart           pass
    Wait For Line On Uart           04 - User mode (MPRV=0, MPP=0) R-- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           Trap! mcause=0x00000007, mepc=0x8000046C, sp=0x80007E24
    Wait For Line On Uart           data mismatch
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           Trap! mcause=0x00000001, mepc=0x80004040, sp=0x80007E34
    Wait For Line On Uart           pass
    Wait For Line On Uart           05 - User mode (MPRV=0, MPP=0) -W- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           06 - User mode (MPRV=0, MPP=0) RW- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           Trap! mcause=0x00000001, mepc=0x80004040, sp=0x80007E34
    Wait For Line On Uart           pass
    Wait For Line On Uart           07 - User mode (MPRV=0, MPP=0) --X from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           Trap! mcause=0x00000007, mepc=0x8000046C, sp=0x80007E24
    Wait For Line On Uart           data mismatch
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           Trap! mcause=0x00000005, mepc=0x800004DC, sp=0x80007DD4
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           08 - User mode (MPRV=0, MPP=0) R-X from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           Trap! mcause=0x00000007, mepc=0x8000046C, sp=0x80007E24
    Wait For Line On Uart           data mismatch
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           09 - User mode (MPRV=0, MPP=0) -WX from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           10 - User mode (MPRV=0, MPP=0) RWX from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           11 - Machine mode (MPRV=0, MPP=0) --- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           12 - Machine mode (MPRV=0, MPP=0) R-- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           13 - Machine mode (MPRV=0, MPP=0) -W- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           14 - Machine mode (MPRV=0, MPP=0) RW- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           15 - Machine mode (MPRV=0, MPP=0) --X from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           16 - Machine mode (MPRV=0, MPP=0) R-X from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           17 - Machine mode (MPRV=0, MPP=0) -WX from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           18 - Machine mode (MPRV=0, MPP=0) RWX from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           19 - Machine mode (MPRV=1, MPP=0) --- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           Trap! mcause=0x00000007, mepc=0x8000046C, sp=0x80007E34
    Wait For Line On Uart           data mismatch
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           Trap! mcause=0x00000005, mepc=0x800004DC, sp=0x80007DE4
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           20 - Machine mode (MPRV=1, MPP=0) R-- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           Trap! mcause=0x00000007, mepc=0x8000046C, sp=0x80007E34
    Wait For Line On Uart           data mismatch
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           21 - Machine mode (MPRV=1, MPP=0) -W- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           22 - Machine mode (MPRV=1, MPP=0) RW- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           23 - Machine mode (MPRV=1, MPP=0) --X from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           Trap! mcause=0x00000007, mepc=0x8000046C, sp=0x80007E34
    Wait For Line On Uart           data mismatch
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           Trap! mcause=0x00000005, mepc=0x800004DC, sp=0x80007DE4
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           24 - Machine mode (MPRV=1, MPP=0) R-X from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           Trap! mcause=0x00000007, mepc=0x8000046C, sp=0x80007E34
    Wait For Line On Uart           data mismatch
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           25 - Machine mode (MPRV=1, MPP=0) -WX from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           26 - Machine mode (MPRV=1, MPP=0) RWX from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           27 - Machine mode (MPRV=1, MPP=1) --- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           28 - Machine mode (MPRV=1, MPP=1) R-- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           29 - Machine mode (MPRV=1, MPP=1) -W- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           30 - Machine mode (MPRV=1, MPP=1) RW- from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           31 - Machine mode (MPRV=1, MPP=1) --X from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           32 - Machine mode (MPRV=1, MPP=1) R-X from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           33 - Machine mode (MPRV=1, MPP=1) -WX from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           34 - Machine mode (MPRV=1, MPP=1) RWX from designated areas
    Wait For Line On Uart           configuring PMP...
    Wait For Line On Uart           testing W...
    Wait For Line On Uart           writing to .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing R...
    Wait For Line On Uart           reading from .area...
    Wait For Line On Uart           data match
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing X...
    Wait For Line On Uart           hello from .area
    Wait For Line On Uart           pass
    Wait For Line On Uart           35 - Testing execution from a locked region in U and M mode
    Wait For Line On Uart           testing from U mode...
    Wait For Line On Uart           Trap! mcause=0x00000001, mepc=0x80004040, sp=0x80007E34
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing from M mode...
    Wait For Line On Uart           Trap! mcause=0x00000001, mepc=0x80004040, sp=0x80007E44
    Wait For Line On Uart           pass
    Wait For Line On Uart           attempting to unlock region...
    Wait For Line On Uart           testing from U mode...
    Wait For Line On Uart           Trap! mcause=0x00000001, mepc=0x80004040, sp=0x80007E34
    Wait For Line On Uart           pass
    Wait For Line On Uart           testing from M mode...
    Wait For Line On Uart           Trap! mcause=0x00000001, mepc=0x80004040, sp=0x80007E44
    Wait For Line On Uart           pass
    Wait For Line On Uart           36/36 passed

    Wait For Line On Uart           Finished: PASSED  matchNextLine=false
