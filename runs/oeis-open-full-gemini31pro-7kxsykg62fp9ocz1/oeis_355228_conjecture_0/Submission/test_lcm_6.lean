import Mathlib
open Finset

def D : Finset ℕ := {1, 2, 3, 4, 6, 8}

#eval D.sum id
#eval D.lcm id
