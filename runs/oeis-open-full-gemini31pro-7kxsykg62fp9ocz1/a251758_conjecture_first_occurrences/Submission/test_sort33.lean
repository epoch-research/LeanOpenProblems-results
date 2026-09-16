import Mathlib

lemma subset_eq_of_length {α : Type*} [DecidableEq α] {l1 l2 : List α} 
  (h_sub : ∀ x, x ∈ l1 → x ∈ l2) (h_nodup1 : l1.Nodup) (h_nodup2 : l2.Nodup)
  (h_len : l1.length = l2.length) : ∀ x, x ∈ l1 ↔ x ∈ l2 := by
  have hs1 : (List.toFinset l1).card = l1.length := List.toFinset_card_of_nodup h_nodup1
  have hs2 : (List.toFinset l2).card = l2.length := List.toFinset_card_of_nodup h_nodup2
  have hsub : List.toFinset l1 ⊆ List.toFinset l2 := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact h_sub x hx
  have heq : List.toFinset l1 = List.toFinset l2 := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hs1, hs2, h_len]
  intro x
  have hx : x ∈ List.toFinset l1 ↔ x ∈ List.toFinset l2 := by rw [heq]
  rw [List.mem_toFinset, List.mem_toFinset] at hx
  exact hx
