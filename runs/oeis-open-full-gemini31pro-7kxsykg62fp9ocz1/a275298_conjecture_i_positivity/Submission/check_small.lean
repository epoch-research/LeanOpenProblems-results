import Mathlib
open Nat Finset Set

def A275298 (n : ℕ) : ℕ :=
  let bound := n + 1
  (range bound).sum fun w =>
    (range bound).sum fun x =>
      (range bound).sum fun y =>
        (range bound).sum fun z =>
          let sum_eq_n : Prop := w^3 + x^2 + y^2 + z^2 = n
          let x_minus_w_sq : Prop := x ≥ w ∧ (sqrt (x - w))^2 = x - w
          let ordering : Prop := y ≤ z ∧ w < z
          if sum_eq_n ∧ x_minus_w_sq ∧ ordering then 1 else 0

def check_all (n : ℕ) : IO Unit := do
  for i in [1:n+1] do
    if A275298 i == 0 then
      IO.println s!"Counterexample: {i}"
  IO.println "Done"

#eval check_all 50
