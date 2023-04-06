#!/usr/bin/env python3
import argparse
import re

# =============================================================================

INSTR_RE = re.compile(r"^\s*(?P<cyc>[0-9]+)\s+:\s+#(?P<inst>[0-9]+)\s+0\s+(?P<pc>[0-9a-f]+)\s+(?P<opc>[0-9a-f]+)\s+(?P<reg>[^=;]+)=(?P<val>[0-9a-f]+)\s+;\s+(?P<mnemonic>.*)")

def parse_log(file_name):

    # Read the log
    with open(file_name, "r") as fp:
        lines = fp.readlines()

    # Parse
    data = []
    for line in lines:

        line  = line.strip()
        match = INSTR_RE.match(line)
        if match is not None:

            entry = (
                match.group("pc"),
                "",
                "{}:{}".format(match.group("reg"), match.group("val")),
                "",
                match.group("opc"),
                "0", # TODO
                match.group("mnemonic"),
                "",
                "",
            )

            data.append(entry)

    return data

def write_csv(file_name, data):

    # Add header
    lines = ["pc,instr,gpr,csr,binary,mode,instr_str,operand,pad"]

    # Add data
    lines.extend([",".join(fields) for fields in data])

    # Write
    with open(file_name, "w") as fp:
        for line in lines:
            fp.write(line + "\n")

# =============================================================================


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--log",
        type=str,
        required=True,
        help="HDL simulation trace log"
    )
    parser.add_argument(
        "--csv",
        type=str,
        required=True,
        help="Output CSV file"
    )

    args = parser.parse_args()

    # Parse log
    data = parse_log(args.log)

    # Write CSV
    write_csv(args.csv, data)

if __name__ == "__main__":
    main()
