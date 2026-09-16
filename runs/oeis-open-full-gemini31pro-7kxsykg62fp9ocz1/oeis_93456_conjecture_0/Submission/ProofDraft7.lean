import FormalConjectures.Util.ProblemImports

open Nat Finset

lemma prod_image_dvd_prod (s : Finset ℕ) (t : Finset ℕ) (f : ℕ → ℕ)
  (h_inj : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y)
  (h_sub : s.image f ⊆ t) :
  (∏ x ∈ s, f x) ∣ (∏ x ∈ t, x) := by
  have H : (∏ x ∈ s, f x) = ∏ x ∈ s.image f, x := by
    exact (prod_image h_inj).symm
  rw [H]
  exact prod_dvd_prod_of_subset h_sub

lemma mem_prod_dvd (s : Finset ℕ) (x : ℕ) (h : x ∈ s) :
  x ∣ ∏ y ∈ s, y := by
  exact dvd_prod_of_mem (fun y => y) h
