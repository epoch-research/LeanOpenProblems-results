import Submission.Spec
import Mathlib

open Nat

def check_div (n : ℕ) : Bool :=
  n ∣ (a (n - 1) + 2 ^ (n - 2))

#eval check_div 3
#eval check_div 5
#eval check_div 6
