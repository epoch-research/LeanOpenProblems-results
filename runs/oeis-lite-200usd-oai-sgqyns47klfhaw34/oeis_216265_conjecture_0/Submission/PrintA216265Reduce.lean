import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)
#reduce A216265 14
#eval A216265 14
#eval A216265 13
#eval A216265 100
