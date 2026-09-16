import Submission.Spec
import Mathlib

open Nat

def check (n : ℕ) : Bool :=
  n ∣ (a (n - 1) + 2 ^ (n - 2))

#eval check 3
#eval check 4
#eval check 5
#eval check 6
#eval check 7
