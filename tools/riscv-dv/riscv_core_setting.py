#!/usr/bin/env python3

import argparse
import hashlib
import logging
import re
from pathlib import Path
from typing import Dict, List, Set

logger = logging.getLogger(__name__)


RISCV_INSTR_PKG_REL_PATH = "src/riscv_instr_pkg.sv"
RISCV_INSTR_PKG_SHA = "90b58f1c998f1116fb4ff8c652a7e7fe4345867739ac4f6f852f452427b0ebed"

VEER_DECODE_REL_PATH = "design/dec/decode"
VEER_DECODE_SHA = "62dc85fad17b27d041678447c401bfee9725d6889a8d4cb68b9e38c34a6b8e79"

VEER_CSRDECODE_REL_PATH = "design/dec/csrdecode"
VEER_CSRDECODE_SHA = "f5ba0a4da487c6f760d20467b4647018eef196b2ad7956f7ee86cea29375796d"

VEER_EL2_DEC_TLU_CTRL_PATH = "design/dec/el2_dec_tlu_ctl.sv"
VEER_EL2_DEC_TLU_CTRL_SHA = "d472b88fd419f8ebd8e1db3ee701b464d02a3cffd8de01aeb702d600736ec547"


def check_sha256(path: Path, exp_sha256: str):
    with open(path, "rb") as fd:
        sha256 = hashlib.sha256(fd.read())
        if sha256.hexdigest() != exp_sha256:
            logger.warning(
                f"Script prepared for a different version of {path} file. ({sha256.hexdigest()} vs {exp_sha256})"
            )
            logger.warning("Verify if the output is correct")


def _parse_enum_with_one_hex(content: List[str], regexp: str, lower: int, upper: int) -> Dict[str, int]:
    result = {}
    for i, line in enumerate(content[lower:upper]):
        reg_data = re.findall(regexp, line)

        if len(reg_data) == 0:
            continue

        if len(reg_data) > 1:
            raise Exception("Found more matching values than expected")

        (name, str_val) = reg_data[0]
        val = int(str_val, 16)
        result[val] = name

    return result


def _parse_enum_with_insn(content: List[str], lower: int, upper: int):
    insn_to_cat = {}
    category = ""
    for i, line in enumerate(content[lower:upper]):
        reg_insn = re.findall(r"^\s*(?<!//)(\b[A-Z0-9_]+\b)", line)
        reg_insn_comment = re.findall(r"//\s*(\bRV[36][24][A-Z0-9]+\b)", line)

        if len(reg_insn) == 0 and len(reg_insn_comment) == 0:
            continue

        if (
            (len(reg_insn) > 0 and len(reg_insn_comment) > 0)
            or (len(reg_insn) > 1)
            or (len(reg_insn_comment) > 1)
        ):
            raise Exception("Found different number of matchin values than expected")

        if len(reg_insn_comment) == 1:
            category = reg_insn_comment[0]

        if len(reg_insn) == 1:
            insn_name = reg_insn[0]

            if category == "":
                raise Exception("Instruction category not found")

            insn_to_cat[insn_name] = category

    return insn_to_cat


def parse_riscv_instr_pkg(riscv_instr_pkg_path: Path):
    """Parses riscv_instr_pkg.sv and returns dictionaries with defined enums"""

    with open(riscv_instr_pkg_path) as fd:
        content = fd.readlines()

    csrs = _parse_enum_with_one_hex(content, r"(\S+)\s*=\s*'h([0-9a-zA-Z]+)", 749, 1101)
    intr = _parse_enum_with_one_hex(content, r"(\S+)\s*=\s*4'h([0-9a-zA-Z]+)", 1146, 1156)
    excp = _parse_enum_with_one_hex(content, r"(\S+)\s*=\s*4'h([0-9a-zA-Z]+)", 1158, 1173)
    insn = _parse_enum_with_insn(content, 115, 649)

    return (csrs, intr, excp, insn)


def _parse_veer_decode(content: List[str], lower: int, upper: int, replace_dict: Dict[str, str] = {}):
    regexp = r"^\s*(?<!\#)\b([a-z0-9_\.]+)[0-9]*\b\s*=\s*\[.*\]"
    veer_insn = set()
    for i, line in enumerate(content[lower:upper]):
        reg_data = re.findall(regexp, line)

        if len(reg_data) == 0:
            continue

        if len(reg_data) != 1:
            raise Exception("Found more matching values than expected")

        veer_insn.add(reg_data[0])

    return veer_insn


def parse_veer_decode(decode_path: Path):
    with open(decode_path) as fd:
        content = fd.readlines()
    return _parse_veer_decode(content, 4, 290)


def _parse_veer_csrdecode(content: List[str], lower: int, upper: int, replace_dict: Dict[str, str] = {}):
    regexp = r"([0-9a-z_]+)\s*=\s*\[([01\.]+)\]"
    veer_csrs = dict()
    for i, line in enumerate(content[lower:upper]):
        reg_data = re.findall(regexp, line)

        if len(reg_data) == 0:
            continue

        if len(reg_data) > 1:
            raise Exception("Found more matching values than expected")

        (name, str_val) = reg_data[0]
        veer_csrs[name] = str_val

    return veer_csrs


def parse_veer_csrdecode(csrdecode_path: Path):
    with open(csrdecode_path) as fd:
        content = fd.readlines()
    return _parse_veer_csrdecode(content, 4, 82)


def _parse_veer_irqs_and_excp(content: List[str], lower: int, upper: int):
    regexp = r"\{5\{.*\}\}\s*&\s*5'h([a-zA-Z0-9]+)"
    result = set()
    for i, line in enumerate(content[lower:upper]):
        reg_data = re.findall(regexp, line)
        if len(reg_data) == 0:
            continue

        if len(reg_data) > 1:
            raise Exception("Not expected")

        str_val = reg_data[0]
        result.add(int(str_val, 16))

    return result


def parse_veer_dec_tlu_ctl(dec_tlu_ctl_path: Path):
    with open(dec_tlu_ctl_path) as fd:
        content = fd.readlines()

    irqs = _parse_veer_irqs_and_excp(content, 983, 988)
    excp = _parse_veer_irqs_and_excp(content, 989, 996)
    return (irqs, excp)


# preparing data


def inv_dict(data: Dict) -> Dict:
    result = {}
    for k, v in data.items():
        result[v] = result.get(v, []) + [k]
    return result


def remove_suffix_number(string: str) -> str:
    return re.sub(r"\d+$", "", string)

def count_nonempty(d: Dict) -> int:
    count = 0
    for k, v in d.items():
        if v:
            count += 1
    return count

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Create VeeR core settings file for riscv-dv")
    parser.add_argument("riscvdv", help="Path to riscv-dv project")
    parser.add_argument("veer", help="Path to veer project")
    args = parser.parse_args()

    # verify arguments

    riscvdv_instr_pkg_path = Path(args.riscvdv, RISCV_INSTR_PKG_REL_PATH)
    if not riscvdv_instr_pkg_path.exists():
        raise FileNotFoundError(f"{riscvdv_instr_pkg_path} not found")
    check_sha256(riscvdv_instr_pkg_path, RISCV_INSTR_PKG_SHA)

    veer_decode_path = Path(args.veer, VEER_DECODE_REL_PATH)
    if not veer_decode_path.exists():
        raise FileNotFoundError(f"{veer_decode_path} not found")
    check_sha256(veer_decode_path, VEER_DECODE_SHA)

    veer_csrdecode_path = Path(args.veer, VEER_CSRDECODE_REL_PATH)
    if not veer_csrdecode_path.exists():
        raise FileNotFoundError(f"{veer_csrdecode_path} not found")
    check_sha256(veer_csrdecode_path, VEER_CSRDECODE_SHA)

    veer_dec_tlu_ctrl_path = Path(args.veer, VEER_EL2_DEC_TLU_CTRL_PATH)
    if not veer_dec_tlu_ctrl_path.exists():
        raise FileNotFoundError(f"{veer_dec_tlu_ctrl_path} not found")
    check_sha256(veer_dec_tlu_ctrl_path, VEER_EL2_DEC_TLU_CTRL_SHA)

    # parse

    (rdv_csrs, rdv_ints, rdv_excs, rdv_insn_to_cat) = parse_riscv_instr_pkg(riscvdv_instr_pkg_path)
    veer_insn: List[str] = parse_veer_decode(veer_decode_path)
    veer_csrs: Dict[str, int] = parse_veer_csrdecode(veer_csrdecode_path)
    (veer_ints, veer_excs) = parse_veer_dec_tlu_ctl(veer_dec_tlu_ctrl_path)

    # adjust data

    rdv_adj_insn_to_cat = dict(rdv_insn_to_cat)
    rdv_adj_insn_to_cat["WFI"] = "RV32I"
    rdv_adj_insn_to_cat["MRET"] = "RV32I"
    rdv_adj_cat_to_insn: Dict[str, str] = inv_dict(rdv_adj_insn_to_cat)

    veer_adj_insn = set()
    for insn in veer_insn:
        if insn == "rev":
            insn = "REV8"
        for x in [
            "pack",
            "grevi",
            "gorci",
            "csrw",
            "csrrwi",
            "csrrs",
            "csrrc",
            "csrrci",
            "csrrw",
        ]:
            if x in insn:
                insn = remove_suffix_number(insn)

        for val, new_val in [(".", "_"), ("_rw", ""), ("_ro", "")]:
            insn = insn.replace(val, new_val)

        veer_adj_insn.add(insn.upper())

    veer_adj_csrs = {int(v.replace(".", "0"), 2): k for k, v in veer_csrs.items()}

    # prepare data

    veer_found_insn: Set[str] = {insn for insn in veer_adj_insn if insn in rdv_adj_insn_to_cat}
    veer_not_found_insn: List[str] = {insn for insn in veer_adj_insn if insn not in rdv_adj_insn_to_cat}
    veer_found_insn_to_cat: Dict[str, str] = {insn: rdv_adj_insn_to_cat[insn] for insn in veer_found_insn}
    veer_found_cat_to_insn: Dict[str, str] = inv_dict(veer_found_insn_to_cat)
    veer_isas: Set[str] = set(veer_found_insn_to_cat.values())

    veer_unsupp_cat_to_insn: Dict[str, str] = {}
    for cat, insns in rdv_adj_cat_to_insn.items():
        if cat in veer_found_cat_to_insn:
            veer_unsupp_cat_to_insn[cat] = set(insns) - set(veer_found_cat_to_insn[cat])

    veer_found_csrs: Dict[str, str] = {
        csr: rdv_csrs[csr] for csr in veer_adj_csrs.keys() if csr in rdv_csrs.keys()
    }
    veer_not_found_csrs: Dict[str, str] = {
        csr: veer_adj_csrs[csr].upper() for csr in (set(veer_adj_csrs.keys() - set(veer_found_csrs.keys())))
    }
    veer_found_ints: Dict[int, str] = {intr: rdv_ints[intr] for intr in veer_ints if intr in rdv_ints}
    veer_not_found_ints: Set[str] = {intr for intr in veer_ints if intr not in rdv_ints}
    veer_found_excs: Dict[int, str] = {excp: rdv_excs[excp] for excp in veer_excs if excp in rdv_excs}
    veer_not_found_excs: Set[str] = {excp for excp in veer_excs if excp not in rdv_excs}

    # print info

    print("//-----------------------------------------------------------------------------")
    print("// Processor feature configuration")
    print("//-----------------------------------------------------------------------------")
    print("//")
    print("parameter int XLEN = 32;")
    print("parameter satp_mode_t SATP_MODE = BARE;")
    print("privileged_mode_t supported_privileged_mode[] = {MACHINE_MODE, USER_MODE};")
    print("")
    print("// NOTE: To get supported and unsupported instructions compare")
    print("// riscv-dv/src/riscv_instr_pkg.sv and Cores-VeeR-EL2/design/dec/decode files")
    print("")
    print("// Unsupported instructions")
    print("riscv_instr_name_t unsupported_instr[] = {")
    cnt = 0
    for i, (cat, insns) in enumerate(veer_unsupp_cat_to_insn.items()):
        if insns:
            sep = "," if cnt != (count_nonempty(veer_unsupp_cat_to_insn) - 1) else ""
            print(f"    {', '.join(insns)}{sep} // {cat}")
            cnt += 1
    print("};")
    print()
    print("// ISA supported by the processor")
    print("riscv_instr_group_t supported_isa[$] = {")
    for i, isa in enumerate(veer_isas):
        sep = "," if i != (len(veer_isas) - 1) else ""
        print(f"    {isa}{sep}")
    print("};")
    print()
    print("// Interrupt mode support")
    print("mtvec_mode_t supported_interrupt_mode[$] = {DIRECT, VECTORED};")
    print("")
    print("// The number of interrupt vectors to be generated, only used if VECTORED interrupt mode is supported")
    print("int max_interrupt_vector_num = 16;")
    print("")
    print("// Physical memory protection support")
    print("bit support_pmp = 1;")
    print("")
    print("// Enhanced physical memory protection support")
    print("// NOTE: Not supported by VeeR, described in:")
    print("// https://raw.githubusercontent.com/riscv/riscv-tee/main/Smepmp/Smepmp.pdf")
    print("bit support_epmp = 0;")
    print("")
    print("// Debug mode support")
    print("bit support_debug_mode = 0;")
    print("")
    print("// Support delegate trap to user mode")
    print("// When implementing UCAUSE, UTVEC, UTVAL, UEPC, USCRATCH, USTATUS, UIE, UIP")
    print("bit support_umode_trap = 0;")
    print("")
    print("// Support sfence.vma instruction")
    print("bit support_sfence = 0;")
    print("")
    print("// Support unaligned load/store")
    print("bit support_unaligned_load_store = 1'b1;")
    print("")
    print("// GPR setting")
    print("parameter int NUM_FLOAT_GPR = 32;")
    print("parameter int NUM_GPR = 32;")
    print("parameter int NUM_VEC_GPR = 32;")
    print("")
    print("// ----------------------------------------------------------------------------")
    print("// Vector extension configuration")
    print("// ----------------------------------------------------------------------------")
    print("// Parameter for vector extension")
    print("parameter int VECTOR_EXTENSION_ENABLE = 0;")
    print("")
    print("parameter int VLEN = 512;")
    print("")
    print("// Maximum size of a single vector element")
    print("parameter int ELEN = 32;")
    print("")
    print("// Minimum size of a sub-element, which must be at most 8-bits.")
    print("parameter int SELEN = 8;")
    print("")
    print("// Maximum size of a single vector element (encoded in vsew format)")
    print("parameter int VELEN = int'($ln(ELEN)/$ln(2)) - 3;")
    print("")
    print("// Maxium LMUL supported by the core")
    print("parameter int MAX_LMUL = 8;")
    print("// ----------------------------------------------------------------------------")
    print("// Multi-harts configuration")
    print("// ----------------------------------------------------------------------------")
    print("")
    print("// Number of harts")
    print("parameter int NUM_HARTS = 1;")
    print("")
    print("// ----------------------------------------------------------------------------")
    print("// Previleged CSR implementation")
    print("// ----------------------------------------------------------------------------")
    print("")
    print("// Implemented previlieged CSR list")
    print("`ifdef DSIM")
    print("privileged_reg_t implemented_csr[] = {")
    print("`else")
    print("const privileged_reg_t implemented_csr[] = {")
    print("`endif")
    for i, (addr, name) in enumerate(veer_found_csrs.items()):
        sep = "," if i != len(veer_found_csrs) - 1 else ""
        print(f"    {name}{sep}")
    print("};")
    print("")
    print("// Implementation-specific custom CSRs")
    print("// By default all not found registers are put to custom csrs")
    print("bit [11:0] custom_csr[] = {")
    for i, (addr, name) in enumerate(veer_not_found_csrs.items()):
        sep = "," if i != len(veer_not_found_csrs) - 1 else ""
        print(f"    12'h{addr:X}{sep} // {name}")
    print("};")
    print("")
    print("// ----------------------------------------------------------------------------")
    print("// Supported interrupt/exception setting, used for functional coverage")
    print("// ----------------------------------------------------------------------------")
    print("")
    print("`ifdef DSIM")
    print("interrupt_cause_t implemented_interrupt[] = {")
    print("`else")
    print("const interrupt_cause_t implemented_interrupt[] = {")
    print("`endif")
    for i, (intr, name) in enumerate(veer_found_ints.items()):
        sep = "," if i != len(veer_found_ints) - 1 else ""
        print(f"    {name}{sep}")
    for i, intr in enumerate(veer_not_found_ints):
        if intr in (list(range(24, 32)) + list(range(48, 64))):
            print(f"    //{hex(intr)} custom interrupt used")
        elif intr in ([14] + list(range(16, 20)) + list(range(32, 48))):
            print(f"    //{hex(intr)} reserved interrupt used")
        else:
            print(f"    //{hex(intr)} not supported")
    print("};")
    print("")
    print("`ifdef DSIM")
    print("exception_cause_t implemented_exception[] = {")
    print("`else")
    print("const exception_cause_t implemented_exception[] = {")
    for i, (exc, name) in enumerate(veer_found_excs.items()):
        sep = "," if i != len(veer_found_excs) - 1 else ""
        print(f"    {name}{sep}")
    for i, exc in enumerate(veer_not_found_excs):
        print(f"    //{hex(exc)} not supported")
    print("};")
    print("`endif")
