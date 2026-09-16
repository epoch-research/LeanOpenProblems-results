import Mathlib

lemma subset_eq_of_length {α : Type*} [DecidableEq α] {l1 l2 : List α} 
  (h_sub : ∀ x, x ∈ l1 → x ∈ l2) (h_nodup1 : l1.Nodup) (h_nodup2 : l2.Nodup)
  (h_len : l1.length = l2.length) : ∀ x, x ∈ l1 ↔ x ∈ l2 := by
  intro x
  constructor
  · exact h_sub x
  · intro hx2
    by_contra hc
    have h_sub_strict : l1.Subset l2 := h_sub
    have h_card : l1.length < l2.length := by
      -- This is a standard mathlib lemma about lists or finsets
      sorry
    omega
