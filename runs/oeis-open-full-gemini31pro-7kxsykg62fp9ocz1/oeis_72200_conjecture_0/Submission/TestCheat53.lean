import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

theorem test : ¬ ((Nat.digits 10 (Nat.factorial 0)).count 6 = 24) := by
  have H : Nat.factorial 0 = 1 := rfl
  rw [H]
  have h_lt : 1 < 10 := by decide
  rw [Nat.digits_of_lt 10 1 (by decide) h_lt]
  decide
