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

def allowed (n : ℕ) : Bool :=
  [7, 9, 19, 49, 133, 589].contains n ||
  (Id.run do
    let mut ok := false
    for k in [0:20] do
      if n == 2^k then ok := true
      if n == 3 * 2^k then ok := true
      for q in [14, 67, 71, 199] do
        if n == 4^k * q then ok := true
    return ok)

def check_range : IO Unit := do
  for n in [1:500] do
    let val := a n
    if val == 0 then
      IO.println s!"Counterexample 0: {n}"
    else if val == 1 then
      if not (allowed n) then
        IO.println s!"Counterexample 1: {n}"
    else
      if allowed n then
        IO.println s!"Counterexample >1: {n}"
  IO.println "Done"

#eval check_range
