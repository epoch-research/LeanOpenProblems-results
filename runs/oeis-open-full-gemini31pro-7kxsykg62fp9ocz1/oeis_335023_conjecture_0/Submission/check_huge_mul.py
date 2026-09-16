import sys
sys.set_int_max_str_digits(10000000)
A = 10**1000000 + 3
B = 10**1000000 + 7
C = A * B
with open('/workspace/leanproject/Submission/TestHugeMult.lean', 'w') as f:
    f.write(f'''import Mathlib
theorem huge_mult : ({A} : ℕ) * {B} = {C} := by decide
''')
