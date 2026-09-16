import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma prod_image_dvd (p M n : ℕ) (S : Finset ℕ) (hp_pos : 0 < p)
  (h_sub : (Icc (M - p + 3) M).image (fun x => p * x) ⊆ S) :
  (∏ x ∈ Icc (M - p + 3) M, (p * x)) ∣ ∏ y ∈ S, y := by
  have H : (∏ x ∈ Icc (M - p + 3) M, (p * x)) = ∏ y ∈ (Icc (M - p + 3) M).image (fun x => p * x), y := by
    apply Eq.symm
    apply prod_image
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hp_pos hab
  rw [H]
  exact prod_dvd_prod_of_subset _ _ id h_sub
