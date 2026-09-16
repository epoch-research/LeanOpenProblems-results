import FormalConjectures.Util.ProblemImports

open Nat Finset

lemma prod_image_dvd_prod (s : Finset ℕ) (t : Finset ℕ) (f : ℕ → ℕ)
  (h_inj : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y)
  (h_sub : s.image f ⊆ t) :
  (∏ x ∈ s, f x) ∣ (∏ x ∈ t, x) := by
  have H : (∏ x ∈ s, f x) = ∏ x ∈ s.image f, x := by
    exact (@prod_image ℕ ℕ _ _ s f h_inj).symm
  rw [H]
  exact prod_dvd_prod_of_subset s.image f t h_sub
