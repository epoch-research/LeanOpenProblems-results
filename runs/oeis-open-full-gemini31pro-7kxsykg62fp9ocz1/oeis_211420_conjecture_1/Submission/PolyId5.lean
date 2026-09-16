import Mathlib

open Nat

lemma odd_even_split (X r : ℤ) (hr : 0 ≤ r) :
  ((List.range r.toNat).map (fun k => 8 * X - 2 * (k:ℤ) - 1)).prod *
  ((List.range r.toNat).map (fun k => 8 * X - 2 * (k:ℤ))).prod
  = ((List.range (2 * r).toNat).map (fun k => 8 * X - (k:ℤ))).prod := by
  sorry
