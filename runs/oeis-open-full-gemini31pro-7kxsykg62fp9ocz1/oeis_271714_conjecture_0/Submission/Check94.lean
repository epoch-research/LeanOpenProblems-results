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

#eval a (66)
#eval a (68)
#eval a (69)
#eval a (70)
#eval a (72)
#eval a (73)
#eval a (74)
#eval a (75)
#eval a (77)
#eval a (78)
