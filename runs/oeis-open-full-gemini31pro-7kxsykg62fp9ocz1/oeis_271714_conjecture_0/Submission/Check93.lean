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

#eval a (54)
#eval a (55)
#eval a (57)
#eval a (58)
#eval a (59)
#eval a (60)
#eval a (61)
#eval a (62)
#eval a (63)
#eval a (65)
