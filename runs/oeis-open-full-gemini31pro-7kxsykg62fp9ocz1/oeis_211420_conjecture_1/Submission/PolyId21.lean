import Submission.PolyId20
import Mathlib

open Nat

lemma descFactorial_eq_prod_even (X : ℕ) (r : ℕ) (hr : r ≤ 4 * X) :
  ((List.range r).map (fun (k:ℕ) => 8 * X - 2 * k)).prod = 2^r * (4 * X).descFactorial r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hr' : r ≤ 4 * X := by omega
    rw [List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [ih hr']
    have H : (4 * X).descFactorial (r + 1) = (4 * X).descFactorial r * (4 * X - r) := by
      -- we want to just say that
      sorry
