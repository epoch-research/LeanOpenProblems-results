import subprocess
import sys

def check_axioms(lean_code):
    with open("/workspace/leanproject/Submission/test_axioms_sorry.lean", "w") as f:
        f.write(lean_code)
    
    # run lean
    res = subprocess.run(["lake", "env", "lean", "Submission/test_axioms_sorry.lean"], capture_output=True, text=True)
    print("STDOUT:")
    print(res.stdout)
    print("STDERR:")
    print(res.stderr)

lean_code = """import FormalConjectures.Util.ProblemImports

open ArithmeticFunction Finset Nat

noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Icc 1 n) fun k : ℕ =>
    (k : ℚ) ^ (moebius k : ℤ)
  ).den

set_option google.answer "always_true"

theorem oeis_a080326_eq_primorial_infinitely_often :
    Set.Infinite {n : ℕ | a n = primorial n} := by
  exact Set.infinite_of_not_bddAbove sorry

#print axioms oeis_a080326_eq_primorial_infinitely_often
"""

check_axioms(lean_code)
