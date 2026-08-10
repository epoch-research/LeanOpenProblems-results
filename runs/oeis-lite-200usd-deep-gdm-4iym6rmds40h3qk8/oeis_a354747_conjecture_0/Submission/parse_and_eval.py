import re
import sys

sys.set_int_max_str_digits(100000)

with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    lines = f.readlines()

defs = {}
# Pattern for def var : Nat := ...
pattern_initial = re.compile(r"def (\w+)\s*:\s*Nat\s*:=\s*(\d+)")
pattern_step = re.compile(r"def (\w+)\s*:\s*Nat\s*:=\s*(\w+)\s*\*\s*10\^100\s*\+\s*(\d+)")

for i, line in enumerate(lines):
    line = line.strip()
    if line.startswith("def ") and "_nat_nat_" in line:
        m = pattern_initial.match(line)
        if m:
            name, val = m.groups()
            defs[name] = int(val)
            continue
        m = pattern_step.match(line)
        if m:
            name, prev, val = m.groups()
            if prev in defs:
                defs[name] = defs[prev] * (10**100) + int(val)
            else:
                print(f"Error: {prev} not defined before {name}")

for name in [
    "alpha_re_val_nat_nat_186",
    "alpha_im_val_nat_nat_186",
    "v2_re_val_nat_nat_186",
    "v3_re_val_nat_nat_186",
    "v3_im_val_nat_nat_186",
    "v100943_re_val_nat_nat_186",
    "v100943_im_val_nat_nat_186"
]:
    val = defs.get(name)
    if val is not None:
        print(f"def {name} : Nat := {val}")
    else:
        print(f"Error: {name} not found!")
