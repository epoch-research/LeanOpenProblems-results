import Mathlib

open Nat

lemma nodup_of_pairwise_lt (L : List ℕ) (h : L.Pairwise (· < ·)) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons hd tl ih =>
    have h1 : tl.Pairwise (· < ·) := List.pairwise_cons.mp h |>.2
    have h2 : ∀ x ∈ tl, hd < x := List.pairwise_cons.mp h |>.1
    have h3 : hd ∉ tl := fun h_in => lt_irrefl hd (h2 hd h_in)
    exact List.nodup_cons.mpr ⟨h3, ih h1⟩
