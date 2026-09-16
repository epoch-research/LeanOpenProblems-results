import Mathlib
open Nat Finset

def a (n : ℕ) : ℕ :=
  let S := range (n.sqrt + 1)
  S.sum fun w =>
  S.sum fun x =>
  S.sum fun y =>
  S.sum fun z =>
    if w > 0 ∧ w^2 + x^2 + y^2 + z^2 = n ∧ IsSquare ((10 * w + 5 * x)^2 + (12 * y + 36 * z)^2)
    then 1
    else 0

#eval a (101)
#eval a (102)
#eval a (103)
#eval a (104)
#eval a (105)
#eval a (106)
#eval a (107)
#eval a (108)
#eval a (109)
#eval a (110)
