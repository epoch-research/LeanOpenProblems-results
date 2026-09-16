import Mathlib

open Nat

lemma list_range_add_two (n : ℕ) :
  List.range (n + 2) = List.range n ++ [n, n + 1] := by
  rw [List.range_succ, List.range_succ]
  simp

lemma odd_even_split (X r : ℕ) :
  ((List.range r).map (fun k => 8 * X - 2 * k - 1)).prod *
  ((List.range r).map (fun k => 8 * X - 2 * k)).prod
  = ((List.range (2 * r)).map (fun k => 8 * X - k)).prod := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.prod_append]
    -- wait, the second list is also succ
    sorry
