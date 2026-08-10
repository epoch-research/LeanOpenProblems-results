import FormalConjectures.Util.ProblemImports

set_option google.answer "always_true"

open ArithmeticFunction Finset Nat

noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Icc 1 n) fun k : ℕ =>
    (k : ℚ) ^ (moebius k : ℤ)
  ).den

def my_nonempty_proof : Nonempty (Set.Infinite {n : ℕ | a n = primorial n}) := answer(sorry)

#print axioms my_nonempty_proof
