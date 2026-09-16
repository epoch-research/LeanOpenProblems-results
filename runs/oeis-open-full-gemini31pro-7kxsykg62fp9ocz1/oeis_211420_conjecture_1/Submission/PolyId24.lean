import Submission.PolyId23
import Mathlib

open Nat

lemma descFactorial_eq_prod_all (X : ℕ) (r : ℕ) (hr : r ≤ 8 * X) :
  ((List.range r).map (fun (k:ℕ) => 8 * X - k)).prod = (8 * X).descFactorial r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hr' : r ≤ 8 * X := by omega
    rw [List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [ih hr']
    have H : (8 * X).descFactorial (r + 1) = (8 * X - r) * (8 * X).descFactorial r := Nat.descFactorial_succ (8 * X) r
    rw [H]
    ring
