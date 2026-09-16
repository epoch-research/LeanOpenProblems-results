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

def check_one (n : ℕ) : Bool :=
  let val := a n
  if val == 0 then true
  else if val == 1 then
    let allowed := [7, 9, 19, 49, 133, 589].contains n
    let allowed := allowed || (∃ k : ℕ, k < 20 ∧ n = 2^k)
    let allowed := allowed || (∃ k : ℕ, k < 20 ∧ n = 3 * 2^k)
    let allowed := allowed || (∃ k : ℕ, k < 20 ∧ ∃ q ∈ [14, 67, 71, 199], n = 4^k * q)
    !allowed
  else
    let allowed := [7, 9, 19, 49, 133, 589].contains n
    let allowed := allowed || (∃ k : ℕ, k < 20 ∧ n = 2^k)
    let allowed := allowed || (∃ k : ℕ, k < 20 ∧ n = 3 * 2^k)
    let allowed := allowed || (∃ k : ℕ, k < 20 ∧ ∃ q ∈ [14, 67, 71, 199], n = 4^k * q)
    allowed

-- Wait, in Lean Decidable exists is not computable for Nat unless bounded. I bounded k to 20.
