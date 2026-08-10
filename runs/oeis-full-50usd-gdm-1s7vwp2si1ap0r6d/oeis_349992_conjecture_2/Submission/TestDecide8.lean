import FormalConjectures.Util.ProblemImports

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

theorem test_decide_1 : generalized_A349992 1 1 11 12 1 > 0 := by decide
theorem test_decide_2 : generalized_A349992 1 1 11 12 2 > 0 := by decide
theorem test_decide_3 : generalized_A349992 1 1 11 12 3 > 0 := by decide
theorem test_decide_4 : generalized_A349992 1 1 11 12 4 > 0 := by decide
theorem test_decide_5 : generalized_A349992 1 1 11 12 5 > 0 := by decide

