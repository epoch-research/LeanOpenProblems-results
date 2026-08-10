import FormalConjectures.Util.ProblemImports

open Nat

def weight_parity_sign (p : ℕ) : ℤ :=
  let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  if (binary_weight p).bodd then 1 else -1

theorem sgn_3 : weight_parity_sign 3 = -1 := by decide
theorem sgn_419 : weight_parity_sign 419 = 1 := by decide
