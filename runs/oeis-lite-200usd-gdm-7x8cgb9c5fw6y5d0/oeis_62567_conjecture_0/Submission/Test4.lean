import FormalConjectures.Util.ProblemImports

open Nat

def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

theorem rev_nine : reverse_nat 9 = 9 := by
  -- We want to simplify reverse_nat 9
  unfold reverse_nat
  simp
