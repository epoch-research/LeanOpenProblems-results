import FormalConjectures.Util.ProblemImports

open Nat Finset

lemma prod_image_dvd_prod (s : Finset ℕ) (t : Finset ℕ) (f : ℕ → ℕ)
  (h_inj : Set.InjOn f ↑s)
  (h_sub : s.image f ⊆ t) :
  (∏ x ∈ s, f x) ∣ (∏ x ∈ t, x) := by
  have H : (∏ x ∈ s.image f, x) = ∏ x ∈ s, f x := by
    exact prod_image h_inj
  rw [← H]
  exact prod_dvd_prod_of_subset (s.image f) t id h_sub
