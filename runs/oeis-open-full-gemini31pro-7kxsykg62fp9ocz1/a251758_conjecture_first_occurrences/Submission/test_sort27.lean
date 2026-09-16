import Mathlib

lemma perm_of_nodup {l1 l2 : List ℕ} (h1 : l1.Nodup) (h2 : l2.Nodup) 
  (h3 : ∀ x, x ∈ l1 ↔ x ∈ l2) : l1.Perm l2 := by apply?
