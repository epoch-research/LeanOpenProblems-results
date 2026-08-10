with open('/workspace/leanproject/Submission/Spec.lean.bak', 'r') as f:
    lines = f.readlines()

# Replace the first line with the correct imports
lines[0] = "import Mathlib.Data.Nat.Fib.Basic\nimport Mathlib.Algebra.Ring.Divisibility.Basic\nimport Mathlib.Data.Int.Basic\nimport Mathlib.Tactic.Linarith\n"

with open('/workspace/leanproject/Submission/test_bak.lean', 'w') as f:
    f.writelines(lines)

print("test_bak.lean created successfully!")
