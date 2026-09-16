import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

def A349992 (n : ℕ) : ℕ :=
  let bound_x : ℕ := Nat.sqrt (Nat.sqrt n) + 1
  let bound_y : ℕ := Nat.sqrt n + 1
  let bound_z : ℕ := (3 * n).sqrt + 1

  (range bound_x).sum fun x =>
  (range bound_y).sum fun y =>
  (range bound_z).sum fun z =>
  (range 2).sum fun w =>
      let num_z_term : ℕ := z ^ 2 + 2 * (4 ^ w)
      if num_z_term % 3 = 0 then
        if n = x ^ 4 + y ^ 2 + num_z_term / 3 then 1 else 0
      else 0

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

theorem oeis_349992_conjecture_2 :
  let tuples : List (ℕ × ℕ × ℕ × ℕ) :=
    [(1,1,11,12), (1,1,11,60), (1,1,14,15), (1,1,23,24), (1,1,23,32),
     (1,1,23,48), (1,2,23,96), (2,1,11,60), (2,1,23,24), (2,1,23,48),
     (4,1,23,48)]
  ∀ (t : ℕ × ℕ × ℕ × ℕ) (h_t : t ∈ tuples) (n : ℕ),
    n > 0 →
    let a := t.1
    let b := t.2.1
    let c := t.2.2.1
    let m := t.2.2.2
    generalized_A349992 a b c m n > 0
  := by sorry

theorem oeis_349992_conjecture_2.disproof : ¬ (type_of% @oeis_349992_conjecture_2) := sorry
