import Mathlib
import Submission.DetAnti
import Submission.DetAnti2

open Equiv Equiv.Perm Finset Matrix

variable {p : ℕ} [NeZero p]

lemma det_anti_triangular {R : Type*} [CommRing R] (M : Matrix (Fin p) (Fin p) R) 
    (hM : ∀ i j : Fin p, p - 1 < (i:ℕ) + (j:ℕ) → M i j = 0) : 
    Matrix.det M = (-1 : R) ^ (p * (p - 1) / 2) * ∏ i : Fin p, M i (revPerm p i) := by
  have H : Matrix.det M = ∑ σ : Perm (Fin p), (Equiv.Perm.sign σ : R) * ∏ i : Fin p, M (σ i) i := Matrix.det_apply' M
  rw [H]
  have H2 : ∑ σ : Perm (Fin p), (Equiv.Perm.sign σ : R) * ∏ i : Fin p, M (σ i) i = 
            (Equiv.Perm.sign (revPerm p) : R) * ∏ i : Fin p, M ((revPerm p) i) i := by
    apply sum_eq_single (revPerm p)
    · intro σ _ h_ne
      have h_not_anti : ¬ (∀ i : Fin p, (i : ℕ) + (σ i : ℕ) ≤ p - 1) := by
        intro h
        have := anti_diagonal_perm_eq_revPerm p σ h
        exact h_ne this
      push_neg at h_not_anti
      rcases h_not_anti with ⟨i, hi⟩
      have h_zero : M (σ i) i = 0 := by
        apply hM
        have : (σ i : ℕ) + (i : ℕ) = (i : ℕ) + (σ i : ℕ) := add_comm _ _
        omega
      have h_prod : (∏ j : Fin p, M (σ j) j) = 0 := Finset.prod_eq_zero (mem_univ i) h_zero
      rw [h_prod, mul_zero]
    · intro h_not_mem
      exfalso
      exact h_not_mem (mem_univ (revPerm p))
  rw [H2]
  have H3 : (Equiv.Perm.sign (revPerm p) : R) = (-1 : R) ^ (p * (p - 1) / 2) := by
    rw [revPerm_sign p]
    simp
  rw [H3]
  have H4 : ∏ i : Fin p, M ((revPerm p) i) i = ∏ i : Fin p, M i (revPerm p i) := by
    have h_prod := Equiv.prod_comp (revPerm p) (fun i => M i (revPerm p i))
    have h_eq : (fun i => M ((revPerm p) i) ((revPerm p) ((revPerm p) i))) = (fun i => M ((revPerm p) i) i) := by
      ext i
      have : (revPerm p) ((revPerm p) i) = i := (revPerm p).left_inv i
      rw [this]
    rw [h_eq] at h_prod
    exact h_prod
  rw [H4]
