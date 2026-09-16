with open("/workspace/leanproject/Submission/AD.lean") as f:
    lines = f.readlines()
for i, l in enumerate(lines):
    if "p.factorial ≡ 1 [MOD q]" in l:
        print(f"Line {i+1}: {l.strip()}")
    if "apply (ZMod.natCast" in l:
        print(f"Line {i+1}: {l.strip()}")
