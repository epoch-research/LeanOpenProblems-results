import Mathlib
import Submission.DetAnti

open Equiv Equiv.Perm Finset Matrix

variable {p : ℕ} [hp : NeZero p]
-- Define the anti-diagonal permutation
def revPerm (p : ℕ) [NeZero p] : Perm (Fin p) where
  toFun := fun i => ⟨p - 1 - i.val, by have : i.val < p := i.isLt; omega⟩
  invFun := fun i => ⟨p - 1 - i.val, by have : i.val < p := i.isLt; omega⟩
  left_inv := fun i => by
    ext
    have : i.val < p := i.isLt
    have hpos : 0 < p := NeZero.pos p
    dsimp
    omega
  right_inv := fun i => by
    ext
    have : i.val < p := i.isLt
    have hpos : 0 < p := NeZero.pos p
    dsimp
    omega

lemma anti_diagonal_perm_eq_revPerm (p : ℕ) [NeZero p] (σ : Perm (Fin p))
    (h : ∀ i : Fin p, (i : ℕ) + (σ i : ℕ) ≤ p - 1) :
    σ = revPerm p := by
  ext i
  have h1 : (i : ℕ) + (σ i : ℕ) = p - 1 := anti_diagonal_perm p (NeZero.pos p) σ h i
  have h2 : (σ i).val = (revPerm p i).val := by 
    dsimp [revPerm]
    omega
  exact h2

lemma revPerm_sign (p : ℕ) [NeZero p] : Equiv.Perm.sign (revPerm p) = (-1 : ℤˣ) ^ (p * (p - 1) / 2) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  have H : ∀ j : Fin p, ∀ i ∈ Iio j, (if (revPerm p) i < (revPerm p) j then (1 : ℤˣ) else (-1 : ℤˣ)) = -1 := by
    intro j i hi
    have h_lt : i < j := by simpa using hi
    have h_val : i.val < j.val := h_lt
    have h_not_lt : ¬ (p - 1 - i.val < p - 1 - j.val) := by omega
    have h_not_lt_fin : ¬ ((revPerm p) i < (revPerm p) j) := by
      intro h
      have : (revPerm p i).val < (revPerm p j).val := h
      exact h_not_lt this
    simp [h_not_lt_fin]
  have H2 : (∏ j : Fin p, ∏ i ∈ Iio j, if (revPerm p) i < (revPerm p) j then (1 : ℤˣ) else (-1 : ℤˣ)) = 
            ∏ j : Fin p, ∏ i ∈ Iio j, (-1 : ℤˣ) := by
    apply prod_congr rfl
    intro j _
    apply prod_congr rfl
    intro i hi
    exact H j i hi
  rw [H2]
  have H3 : ∀ j : Fin p, ∏ i ∈ Iio j, (-1 : ℤˣ) = (-1 : ℤˣ) ^ (j.val) := by
    intro j
    rw [prod_const, Fin.card_Iio j]
  have H4 : (∏ j : Fin p, ∏ i ∈ Iio j, (-1 : ℤˣ)) = ∏ j : Fin p, (-1 : ℤˣ) ^ (j.val) := by
    apply prod_congr rfl
    intro j _
    exact H3 j
  rw [H4, Finset.prod_pow_eq_pow_sum]
  have H5 : ∑ j : Fin p, j.val = p * (p - 1) / 2 := by
    have := sum_fin_nat p
    omega
  rw [H5]
