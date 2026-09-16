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

#eval a 7
#eval a 9
#eval a 19
#eval a 49
#eval a 133
#eval a 589
#eval a 14
#eval a 67
#eval a 71
#eval a 199
#eval a 2
#eval a 3
#eval a 1
#eval a 28
#eval a 76
#eval a 36
#eval a 112
#eval a 589
#eval a (1000)
