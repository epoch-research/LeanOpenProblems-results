import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

def recBad (n : ℕ) (h : n > 13) : A216265 n > 0 := recBad n h
termination_by n
-- decreasing_by ?
