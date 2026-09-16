import sys
with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    text = f.read()

text = text.replace("    a N = if F33.Prime then F33 else 2 ^ (N + 1) := by", "    a N = if Nat.Prime F33 then F33 else 2 ^ (N + 1) := by")

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write(text)
