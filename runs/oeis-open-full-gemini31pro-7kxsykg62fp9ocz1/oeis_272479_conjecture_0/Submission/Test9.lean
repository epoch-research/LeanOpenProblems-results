import Mathlib

open Nat
open Finset

lemma sum_toFinset_eq_sum_map (X : List ℕ) (h_distinct : X.Nodup) :
    ∑ i ∈ X.toFinset, 10 ^ i = (X.map (fun x => 10^x)).sum := by
  induction X with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
    have h1 : hd ∉ tl := List.nodup_cons.mp h_distinct |>.1
    have h2 : tl.Nodup := List.nodup_cons.mp h_distinct |>.2
    have h3 : hd ∉ tl.toFinset := by simp [h1]
    rw [sum_insert h3, ih h2]
