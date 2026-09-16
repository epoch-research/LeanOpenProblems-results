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

def check_range : ℕ :=
  Id.run do
    let mut bad := 0
    for n in [1:201] do
      if a n == 1 then
        let allowed := [7, 9, 19, 49, 133, 589].contains n
                       || (∃ k, n == 2^k)
                       || (∃ k, n == 3 * 2^k)
                       || (∃ k q, [14, 67, 71, 199].contains q ∧ n == 4^k * q)
        -- since I can't easily eval exists in Id.run, I will just do it naively.
    return 0

