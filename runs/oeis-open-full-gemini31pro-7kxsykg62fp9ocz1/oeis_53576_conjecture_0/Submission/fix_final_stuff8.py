import sys
with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    text = f.read()

text = text.replace("    a N = if Nat.Prime F33 then F33 else 2 ^ (N + 1) := by\ntheorem oeis_53576_conjecture_0.disproof", "    a N = if Nat.Prime F33 then F33 else 2 ^ (N + 1) := by\n  sorry\n\ntheorem oeis_53576_conjecture_0.disproof")

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write(text)
