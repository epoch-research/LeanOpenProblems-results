import FormalConjectures.Util.ProblemImports

open Nat

example : Nat.sqrt 3 = 1 := by
  have h1 : 1 ≤ Nat.sqrt 3 := by
    rw [le_sqrt]
    decide
  have h2 : Nat.sqrt 3 < 2 := by
    rw [lt_iff_not_ge]
    intro h
    rw [le_sqrt] at h
    contradiction
  omega
