import FormalConjectures.Util.ProblemImports

open Nat Finset

lemma prod_image_dvd_prod {α : Type} [DecidableEq α] (s : Finset α) (t : Finset α) (f : α → α)
  (h_inj : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y)
  (h_sub : s.image f ⊆ t) :
  (∏ x ∈ s, f x) ∣ (∏ x ∈ t, x) := by
  have : (∏ x ∈ s, f x) = ∏ x ∈ s.image f, x := by
    exact (prod_image h_inj).symm
  rw [this]
  exact prod_dvd_prod_of_subset h_sub

lemma dvd_prod_of_mem {α : Type} (s : Finset α) (x : α) (h : x ∈ s) (f : α → ℕ) :
  f x ∣ ∏ y ∈ s, f y := by
  exact dvd_prod_of_mem f h
