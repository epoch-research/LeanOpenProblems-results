import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

theorem test : ¬ ((Nat.digits 10 (Nat.factorial 0)).count 6 = 24) := by
  have H : Nat.factorial 0 = 1 := rfl
  rw [H]
  have H2 : Nat.digits 10 1 = [1] := by rfl
  rw [H2]
  rfl
