import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

-- Check exact values around the known zeros using norm_num/decide where finite.
#eval A216265 13
#eval A216265 14
#eval A216265 20
#eval A216265 81
#eval A216265 82
