import Submission.PolyId32
import Mathlib

open Nat

lemma descFactorial_eq_prod_all (X : ℕ) (r : ℕ) (hr : r ≤ 8 * X) :
  ((List.range r).map (fun (k:ℕ) => (8 * (X:ℤ) - (k:ℤ)))).prod = ((8 * X).descFactorial r : ℤ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hr' : r ≤ 8 * X := by omega
    have h_r1 : List.range (r + 1) = List.range r ++ [r] := by rw [List.range_succ]
    rw [h_r1, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [ih hr']
    have H : (8 * X).descFactorial (r + 1) = (8 * X - r) * (8 * X).descFactorial r := Nat.descFactorial_succ (8 * X) r
    rw [H]
    push_cast
    have H2 : ((8 * X - r : ℕ) : ℤ) = 8 * (X:ℤ) - (r:ℤ) := by
      exact Nat.cast_sub hr'
    rw [H2]
    ring
