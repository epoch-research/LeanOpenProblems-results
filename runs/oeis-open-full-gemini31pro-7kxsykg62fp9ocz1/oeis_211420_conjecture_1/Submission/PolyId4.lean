import Mathlib

open Nat

lemma odd_even_split (X r : ℕ) :
  ((List.range r).map (fun k => 8 * X - 2 * k - 1)).prod *
  ((List.range r).map (fun k => 8 * X - 2 * k)).prod
  = ((List.range (2 * r)).map (fun k => 8 * X - k)).prod := by
  induction r with
  | zero => simp
  | succ r ih =>
    have H2 : 2 * (r + 1) = 2 * r + 2 := by omega
    rw [H2]
    have L1 : List.range (r + 1) = List.range r ++ [r] := List.range_succ r
    have L2 : List.range (2 * r + 2) = List.range (2 * r) ++ [2 * r, 2 * r + 1] := by
      rw [List.range_succ, List.range_succ]
      simp
    rw [L1, L2]
    simp only [List.map_append, List.prod_append, List.map_cons, List.prod_cons, List.prod_nil, mul_one]
    -- Now we have:
    -- (prod1 * (8*X - 2*r - 1)) * (prod2 * (8*X - 2*r)) = prod3 * (8*X - 2*r) * (8*X - (2*r + 1))
    -- Using ih: prod1 * prod2 = prod3.
    -- We just need ring.
    linarith
