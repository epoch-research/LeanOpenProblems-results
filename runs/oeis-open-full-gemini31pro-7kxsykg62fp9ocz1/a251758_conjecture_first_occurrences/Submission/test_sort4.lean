import Mathlib

lemma list_eq_of_sorted_nodup {α : Type*} [LinearOrder α] {l₁ l₂ : List α} 
  (h1 : l₁.Pairwise (· ≤ ·)) (h2 : l₂.Pairwise (· ≤ ·)) 
  (h3 : l₁.Nodup) (h4 : l₂.Nodup) 
  (h5 : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ := by apply?
