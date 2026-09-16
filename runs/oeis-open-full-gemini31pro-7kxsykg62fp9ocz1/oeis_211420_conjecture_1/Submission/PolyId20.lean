import Mathlib

open Nat

lemma list_range_append_two (n : ℕ) :
  List.range (n + 2) = List.range n ++ [n, n + 1] := by
  change List.range (n + 1 + 1) = List.range n ++ [n, n + 1]
  rw [List.range_succ, List.range_succ, List.append_assoc]
  rfl

lemma odd_even_split_nat (X : ℕ) (r : ℕ) (hr : 2 * r ≤ 8 * X) :
  ((List.range r).map (fun (k:ℕ) => 8 * X - 2 * k - 1)).prod *
  ((List.range r).map (fun (k:ℕ) => 8 * X - 2 * k)).prod
  = ((List.range (2 * r)).map (fun (k:ℕ) => 8 * X - k)).prod := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hr' : 2 * r ≤ 8 * X := by omega
    have H2 : 2 * (r + 1) = 2 * r + 2 := by omega
    rw [H2]
    change ((List.range (r + 1)).map _).prod * ((List.range (r + 1)).map _).prod = _
    rw [List.range_succ, list_range_append_two (2 * r)]
    rw [List.map_append, List.prod_append]
    rw [List.map_append, List.prod_append]
    rw [List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have h_ring :
      (((List.range r).map (fun (k:ℕ) => 8 * X - 2 * k - 1)).prod * (8 * X - 2 * r - 1)) *
      (((List.range r).map (fun (k:ℕ) => 8 * X - 2 * k)).prod * (8 * X - 2 * r))
      =
      (((List.range r).map (fun (k:ℕ) => 8 * X - 2 * k - 1)).prod *
       ((List.range r).map (fun (k:ℕ) => 8 * X - 2 * k)).prod) *
      ((8 * X - 2 * r - 1) * (8 * X - 2 * r)) := by ring
    rw [h_ring]
    rw [ih hr']
    have H3 : 8 * X - (2 * r + 1) = 8 * X - 2 * r - 1 := by omega
    have H4 : (8 * X - 2 * r - 1) * (8 * X - 2 * r) = (8 * X - 2 * r) * (8 * X - (2 * r + 1)) := by
      rw [H3, mul_comm]
    rw [H4]
