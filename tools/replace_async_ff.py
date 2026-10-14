#!/usr/bin/env python3

"""Replace the generated ASAP7 async DFF model with the simulation model used here."""

from pathlib import Path
import re
import sys


path = Path(sys.argv[1])
text = path.read_text(encoding="utf8")
pattern = r"module\s+DFFASRHQNx1_ASAP7_75t_R\s*\(.*?endmodule"
replacement = """module DFFASRHQNx1_ASAP7_75t_R (QN, D, RESETN, SETN, CLK);
    output reg QN;
    input D, RESETN, SETN, CLK;
    always @(posedge CLK or negedge RESETN or negedge SETN) begin
        if (!SETN)        QN <= 1'b0;
        else if (!RESETN) QN <= 1'b1;
        else              QN <= ~D;
    end
endmodule"""

text, replacements = re.subn(pattern, lambda _: replacement, text, flags=re.S)
if replacements != 1:
    raise SystemExit(
        f"No DFFASRHQNx1_ASAP7_75t_R module instances; found {replacements}"
    )
path.write_text(text, encoding="utf8")
