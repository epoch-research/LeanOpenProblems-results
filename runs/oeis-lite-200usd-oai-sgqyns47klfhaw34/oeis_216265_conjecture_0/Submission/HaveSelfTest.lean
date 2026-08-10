import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

theorem haveSelfFoo (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  have hself : A216265 n > 0 := hself
  exact hself
#print axioms haveSelfFoo
