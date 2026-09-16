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
    have H : (4 * X).descFactorial (r + 1) = (4 * X - r) * (4 * X).descFactorial r := Nat.descFactorial_succ (4 * X) r
    rw [H, pow_succ]
    calc
      2^r * (4 * X).descFactorial r * (8 * X - 2 * r)
      _ = 2^r * (4 * X).descFactorial r * (2 * (4 * X - r)) := by
        have h_eq : 8 * X - 2 * r = 2 * (4 * X - r) := by omega
        rw [h_eq]
      _ = 2^r * 2 * ((4 * X - r) * (4 * X).descFactorial r) := by ring
