import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

mutual
  theorem mf1 (n : ℕ) (h : n > 13) : A216265 n > 0 := mf2 n h
  theorem mf2 (n : ℕ) (h : n > 13) : A216265 n > 0 := mf1 n h
end
#print axioms mf1
