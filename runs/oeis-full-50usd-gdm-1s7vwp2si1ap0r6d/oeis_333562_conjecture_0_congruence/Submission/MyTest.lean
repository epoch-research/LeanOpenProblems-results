import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (3 * n + 1)) fun j =>
    (n + j - 1).choose j * (2 ^ j)

theorem a_0_eq_1 : a 0 = 1 := by rfl
theorem a_1_eq_15 : a 1 = 15 := by rfl

#check (· ≡ · [MOD ·])
#print Nat.ModEq









