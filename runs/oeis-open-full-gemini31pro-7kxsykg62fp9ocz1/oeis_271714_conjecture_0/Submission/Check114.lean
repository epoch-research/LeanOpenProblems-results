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

def is_pow2 : ℕ → Bool
  | 0 => false
  | 1 => true
  | n + 2 => if (n + 2) % 2 == 0 then is_pow2 ((n + 2) / 2) else false

def is_pow4 : ℕ → Bool
  | 0 => false
  | 1 => true
  | n + 2 => if (n + 2) % 4 == 0 then is_pow4 ((n + 2) / 4) else false

def check_allow (n : ℕ) : Bool :=
  [7, 9, 19, 49, 133, 589].contains n ||
  is_pow2 n ||
  (n % 3 == 0 && is_pow2 (n / 3)) ||
  (n % 14 == 0 && is_pow4 (n / 14)) ||
  (n % 67 == 0 && is_pow4 (n / 67)) ||
  (n % 71 == 0 && is_pow4 (n / 71)) ||
  (n % 199 == 0 && is_pow4 (n / 199))

def find_counterexample : IO Unit := do
  for n in [1:700] do
    let val := a n
    if val == 0 then
      IO.println s!"Counterexample 0: {n}"
    else if val == 1 then
      if !check_allow n then
        IO.println s!"Counterexample 1: {n}"
    else
      if check_allow n then
        IO.println s!"Counterexample >1: {n} (a={val})"

#eval find_counterexample
