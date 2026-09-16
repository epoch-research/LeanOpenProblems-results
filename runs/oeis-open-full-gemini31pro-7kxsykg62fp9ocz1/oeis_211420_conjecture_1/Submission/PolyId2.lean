import Mathlib

open Nat

lemma odd_even_split (X r : ℕ) :
  ((List.range r).map (fun k => 8 * X - 2 * k - 1)).prod *
  ((List.range r).map (fun k => 8 * X - 2 * k)).prod
  = ((List.range (2 * r)).map (fun k => 8 * X - k)).prod := by
  induction r with
  | zero => simp
  | succ r ih =>
    -- how to step?
    sorry
