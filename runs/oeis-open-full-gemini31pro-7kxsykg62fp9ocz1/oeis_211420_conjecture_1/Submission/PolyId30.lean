import Mathlib

open Nat

lemma odd_even_split (X : ℤ) (r : ℕ) :
  ((List.range r).map (fun (k:ℕ) => 8 * X - 2 * (k:ℤ) - 1)).prod *
  ((List.range r).map (fun (k:ℕ) => 8 * X - 2 * (k:ℤ))).prod
  = ((List.range (2 * r)).map (fun (k:ℕ) => 8 * X - (k:ℤ))).prod := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h_r1 : List.range (r + 1) = List.range r ++ [r] := List.range_succ r
    -- We can use h_r1 to rewrite the LHS
    -- First, let's target the exact instances
    have L1 : ((List.range (r + 1)).map (fun (k:ℕ) => 8 * X - 2 * (k:ℤ) - 1)).prod = ((List.range r).map (fun (k:ℕ) => 8 * X - 2 * (k:ℤ) - 1)).prod * (8 * X - 2 * (r:ℤ) - 1) := by
      rw [h_r1, List.map_append, List.prod_append]
      simp
    have L2 : ((List.range (r + 1)).map (fun (k:ℕ) => 8 * X - 2 * (k:ℤ))).prod = ((List.range r).map (fun (k:ℕ) => 8 * X - 2 * (k:ℤ))).prod * (8 * X - 2 * (r:ℤ)) := by
      rw [h_r1, List.map_append, List.prod_append]
      simp
    rw [L1, L2]
    have H : 2 * (r + 1) = 2 * r + 2 := by omega
    rw [H]
    have h_range : List.range (2 * r + 2) = List.range (2 * r) ++ [2 * r, 2 * r + 1] := by
      change List.range (2 * r + 1 + 1) = _
      rw [List.range_succ, List.range_succ, List.append_assoc]
      rfl
    rw [h_range]
    rw [List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_two]
    have H_ring : (((List.range r).map (fun (k:ℕ) => 8 * X - 2 * (k:ℤ) - 1)).prod * (8 * X - 2 * (r:ℤ) - 1)) *
        (((List.range r).map (fun (k:ℕ) => 8 * X - 2 * (k:ℤ))).prod * (8 * X - 2 * (r:ℤ))) = 
        (((List.range r).map (fun (k:ℕ) => 8 * X - 2 * (k:ℤ) - 1)).prod *
           ((List.range r).map (fun (k:ℕ) => 8 * X - 2 * (k:ℤ))).prod) *
          ((8 * X - 2 * (r:ℤ) - 1) * (8 * X - 2 * (r:ℤ))) := by ring
    rw [H_ring]
    rw [ih]
    ring
