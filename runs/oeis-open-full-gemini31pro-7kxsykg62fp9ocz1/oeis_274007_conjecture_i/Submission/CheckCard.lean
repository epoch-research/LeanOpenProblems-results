import Mathlib
open Finset

def check_card (n : ℕ) : Bool :=
  let B := range (n + 1)
  card ((B.product B).product (B.product B)) == (n + 1)^4

#eval check_card 5
#eval check_card 10
