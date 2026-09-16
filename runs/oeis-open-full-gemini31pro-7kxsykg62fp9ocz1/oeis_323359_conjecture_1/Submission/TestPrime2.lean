import Mathlib
open Nat

def check_comp (n : ℕ) : Bool :=
  if n > 0 && n != 1 && !n.Prime then true else false

#eval check_comp 4
#eval check_comp 5
#eval check_comp 6
#eval check_comp 7
