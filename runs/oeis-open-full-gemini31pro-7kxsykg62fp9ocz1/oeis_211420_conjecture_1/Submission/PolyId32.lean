import Submission.PolyId31
import Mathlib

open Nat

lemma descFactorial_eq_prod_even (X : ℕ) (r : ℕ) (hr : r ≤ 4 * X) :
  ((List.range r).map (fun (k:ℕ) => (8 * (X:ℤ) - 2 * (k:ℤ)))).prod = (2:ℤ)^r * ((4 * X).descFactorial r : ℤ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hr' : r ≤ 4 * X := by omega
    have h_r1 : List.range (r + 1) = List.range r ++ [r] := by rw [List.range_succ]
    rw [h_r1, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [ih hr']
    have H : (4 * X).descFactorial (r + 1) = (4 * X - r) * (4 * X).descFactorial r := Nat.descFactorial_succ (4 * X) r
    rw [H]
    push_cast
    have H2 : 8 * (X:ℤ) - 2 * (r:ℤ) = 2 * ((4 * X - r : ℕ) : ℤ) := by
      push_cast
      have h_sub : ((4 * X - r : ℕ) : ℤ) = 4 * X - r := by
        exact Nat.cast_sub hr'
      rw [h_sub]
      ring
    rw [H2]
    ring
