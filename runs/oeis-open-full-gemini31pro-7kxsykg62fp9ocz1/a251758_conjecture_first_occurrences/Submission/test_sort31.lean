import Mathlib

lemma subset_eq_of_length {α : Type*} [DecidableEq α] {l1 l2 : List α} 
  (h_sub : ∀ x, x ∈ l1 → x ∈ l2) (h_nodup1 : l1.Nodup) (h_nodup2 : l2.Nodup)
  (h_len : l1.length = l2.length) : ∀ x, x ∈ l1 ↔ x ∈ l2 := by
  sorry
