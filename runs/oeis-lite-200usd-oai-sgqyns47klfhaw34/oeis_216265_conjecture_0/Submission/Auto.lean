import FormalConjectures.Util.ProblemImports

open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

example (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  positivity

example (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  aesop

example (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  simp [A216265]
