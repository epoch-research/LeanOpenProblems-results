with open('/workspace/leanproject/Submission/test_gcd_proof7.lean', 'r') as f:
    lines = f.readlines()

lines[0] = "import Mathlib.Data.Nat.Fib.Basic\nimport Mathlib.Algebra.Ring.Divisibility.Basic\nimport Mathlib.Data.Int.Basic\nimport Mathlib.Tactic.Linarith\n"

with open('/workspace/leanproject/Submission/test_proof7_run.lean', 'w') as f:
    f.writelines(lines)

print("test_proof7_run.lean created successfully!")
