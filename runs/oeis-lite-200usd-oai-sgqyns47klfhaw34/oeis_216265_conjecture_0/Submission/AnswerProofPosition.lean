import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

theorem bad (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  exact answer(sorry)
#print axioms bad
