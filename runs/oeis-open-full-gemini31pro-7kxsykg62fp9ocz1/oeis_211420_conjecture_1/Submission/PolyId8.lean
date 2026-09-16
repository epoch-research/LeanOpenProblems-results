import Mathlib

open Nat

lemma odd_even_split (X : ℤ) (r : ℕ) :
  ((List.range r).map (fun k => 8 * X - 2 * (k:ℤ) - 1)).prod *
  ((List.range r).map (fun k => 8 * X - 2 * (k:ℤ))).prod
  = ((List.range (2 * r)).map (fun k => 8 * X - (k:ℤ))).prod := by
  induction r with
  | zero => simp
  | succ r ih =>
    have H2 : 2 * (r + 1) = 2 * r + 2 := by omega
    rw [H2]
    have L1 : List.range (r + 1) = List.range r ++ [r] := List.range_succ
    have L2 : List.range (2 * r + 2) = List.range (2 * r) ++ [2 * r, 2 * r + 1] := by
      rw [List.range_succ, List.range_succ]
      rfl
    rw [L1, L2]
    rw [List.map_append, List.prod_append]
    rw [List.map_append, List.prod_append]
    rw [List.map_append, List.prod_append]
    simp only [List.map_cons, List.prod_cons, List.prod_nil, mul_one]
    calc
      _ = (((List.range r).map (fun k => 8 * X - 2 * (k:ℤ) - 1)).prod * (8 * X - 2 * (r:ℤ) - 1)) *
          (((List.range r).map (fun k => 8 * X - 2 * (k:ℤ))).prod * (8 * X - 2 * (r:ℤ))) := by ring
      _ = (((List.range r).map (fun k => 8 * X - 2 * (k:ℤ) - 1)).prod *
           ((List.range r).map (fun k => 8 * X - 2 * (k:ℤ))).prod) *
          ((8 * X - 2 * (r:ℤ) - 1) * (8 * X - 2 * (r:ℤ))) := by ring
      _ = ((List.range (2 * r)).map (fun k => 8 * X - (k:ℤ))).prod *
          ((8 * X - 2 * (r:ℤ) - 1) * (8 * X - 2 * (r:ℤ))) := by rw [ih]
      _ = ((List.range (2 * r)).map (fun k => 8 * X - (k:ℤ))).prod *
          ((8 * X - (2 * (r:ℤ))) * (8 * X - (2 * (r:ℤ) + 1))) := by ring
