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

#eval a (90)
#eval a (91)
#eval a (92)
#eval a (93)
#eval a (94)
#eval a (95)
#eval a (97)
#eval a (98)
#eval a (99)
#eval a (100)
