import Mathlib

open Nat

def A038107 (n : ℕ) : ℕ := (Nat.primesBelow (n ^ 2)).card

#eval A038107 2
#eval A038107 3
#eval A038107 4
#eval A038107 5
#eval A038107 6
