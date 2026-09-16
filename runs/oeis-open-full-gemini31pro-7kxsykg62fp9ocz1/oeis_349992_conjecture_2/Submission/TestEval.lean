import Mathlib

open Nat Finset BigOperators

def generalized_A349992 (a b c m n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let bound_x : ℕ := Nat.sqrt (Nat.sqrt (n / a)) + 1
  let bound_y : ℕ := Nat.sqrt (n / b) + 1

  (range bound_x).sum fun x =>
  (range bound_y).sum fun y =>
  (range 2).sum fun w =>
    let full_sum : ℕ := a * x ^ 4 + b * y ^ 2
    let c_term : ℕ := c * 4 ^ w

    if full_sum < n ∧ m > 0 then
      let target_z2 : ℕ := m * (n - full_sum) - c_term
      if c_term ≤ m * (n - full_sum) ∧ (Nat.sqrt target_z2) ^ 2 = target_z2 then
        1
      else
        0
    else
      0

def eval_test (limit : ℕ) : IO Unit := do
  let tuples := [(1,1,11,12), (1,1,11,60), (1,1,14,15), (1,1,23,24), (1,1,23,32),
                 (1,1,23,48), (1,2,23,96), (2,1,11,60), (2,1,23,24), (2,1,23,48),
                 (4,1,23,48)]
  for t in tuples do
    for n in List.range limit do
      if n > 0 then
        if generalized_A349992 t.1 t.2.1 t.2.2.1 t.2.2.2 n == 0 then
          IO.println s!"Counterexample found: {t} {n}"
          return
  IO.println "Done checking up to limit."

def main : IO Unit := eval_test 10000

