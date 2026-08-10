import FormalConjectures.Util.ProblemImports

open ArithmeticFunction Finset Nat

noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Icc 1 n) fun k : ℕ =>
    (k : ℚ) ^ (moebius k : ℤ)
  ).den

example : a 30 = primorial 30 := by decide
