import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

def generalized_A349992 (a b c m n : ℕ) : ℕ :=
  if n = 0 then 0 else
  -- Bound for x: x^4 <= n/a => x <= (n/a)^(1/4)
  let bound_x : ℕ := Nat.sqrt (Nat.sqrt (n / a)) + 1
  -- Bound for y: y^2 <= n/b => y <= (n/b)^(1/2)
  let bound_y : ℕ := Nat.sqrt (n / b) + 1

  (range bound_x).sum fun x =>
  (range bound_y).sum fun y =>
  (range 2).sum fun w =>
    let full_sum : ℕ := a * x ^ 4 + b * y ^ 2
    let c_term : ℕ := c * 4 ^ w

    -- Check if the remaining part of n is positive
    if full_sum < n ∧ m > 0 then
      -- We are looking for z such that: m * (n - full_sum) = z^2 + c_term
      let target_z2 : ℕ := m * (n - full_sum) - c_term

      -- Check that z^2 is non-negative (i.e., c_term <= m * (n - full_sum))
      -- and that the resulting target is a perfect square.
      if c_term ≤ m * (n - full_sum) ∧ (Nat.sqrt target_z2) ^ 2 = target_z2 then
        1
      else
        0
    else
      0

def check_all_tuples_lean : Bool :=
  let tuples : List (ℕ × ℕ × ℕ × ℕ) :=
    [(1,1,11,12), (1,1,11,60), (1,1,14,15), (1,1,23,24), (1,1,23,32),
     (1,1,23,48), (1,2,23,96), (2,1,11,60), (2,1,23,24), (2,1,23,48),
     (4,1,23,48)]
  tuples.all fun t =>
    let a := t.1
    let b := t.2.1
    let c := t.2.2.1
    let m := t.2.2.2
    (List.range 1001).all fun n =>
      if n = 0 then true else
      generalized_A349992 a b c m n > 0

#eval check_all_tuples_lean
