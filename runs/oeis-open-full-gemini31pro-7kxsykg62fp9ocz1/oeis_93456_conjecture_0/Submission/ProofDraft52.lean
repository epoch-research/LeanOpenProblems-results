import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  let L := n.choose 2 + 1
  let R := (n + 1).choose 2
  let is_composite (k : ℕ) : Prop := 1 < k ∧ ¬ k.Prime
  (Icc L R).filter is_composite |>.prod id

lemma prod_image_dvd (p M : ℕ) (S : Finset ℕ) (hp_pos : 0 < p)
  (h_sub : (Icc (M - p + 3) M).image (fun x => p * x) ⊆ S) :
  (∏ x ∈ Icc (M - p + 3) M, (p * x)) ∣ ∏ y ∈ S, y := by
  have H : (∏ x ∈ Icc (M - p + 3) M, (p * x)) = ∏ y ∈ (Icc (M - p + 3) M).image (fun x => p * x), y := by
    apply Eq.symm
    apply prod_image
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hp_pos hab
  rw [H]
  exact prod_dvd_prod_of_subset _ _ id h_sub

lemma prod_px (p M : ℕ) (hp5 : 5 ≤ p) (hM : p ≤ M) :
  (∏ x ∈ Icc (M - p + 3) M, (p * x)) = p^(p - 2) * ∏ x ∈ Icc (M - p + 3) M, x := by
  rw [prod_mul_distrib, prod_const]
  congr 1
  have : (Icc (M - p + 3) M).card = p - 2 := by
    rw [Nat.card_Icc]
    zify [show p ≤ M by omega]
    omega
  rw [this]

lemma p_dvd_prod_x (p M : ℕ) (hp5 : 5 ≤ p) (hM : p ≤ M) (hp_dvd : p ∣ M - 1) :
  p ∣ ∏ x ∈ Icc (M - p + 3) M, x := by
  have H : M - 1 ∈ Icc (M - p + 3) M := by
    rw [mem_Icc]
    constructor <;> omega
  exact dvd_trans hp_dvd (dvd_prod_of_mem (fun x => x) H)

