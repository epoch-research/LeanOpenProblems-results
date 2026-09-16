import Mathlib

open Nat

def isEven (n : ℕ) : Bool := n % 2 == 0

#eval Nat.nth (fun n => n % 2 = 0) 0
#eval Nat.nth (fun n => n % 2 = 0) 1
