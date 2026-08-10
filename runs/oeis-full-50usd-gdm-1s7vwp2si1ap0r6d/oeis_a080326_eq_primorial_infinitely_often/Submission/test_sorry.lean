import FormalConjectures.Util.ProblemImports

open ArithmeticFunction Finset Nat

noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Icc 1 n) fun k : ℕ =>
    (k : ℚ) ^ (moebius k : ℤ)
  ).den

set_option google.answer "always_true"

theorem oeis_a080326_eq_primorial_infinitely_often :
    Set.Infinite {n : ℕ | a n = primorial n} := answer(sorry)

#print axioms oeis_a080326_eq_primorial_infinitely_often
