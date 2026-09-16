import Mathlib
import Submission.Spec2_part2
import Submission.Spec2_part3
import Submission.SpecPell
import Submission.Spec4
import Submission.SpecSum

lemma bound_2P (j k : ℕ) (hj : 0 < j) (hk2 : k ≤ (P (2*j-1)).toNat) :
  2 * (k : ℤ)^2 ≤ (P (2*j))^2 - 1 := by
  have hk_bound : (k:ℤ) ≤ P (2*j-1) := by
    have : (k:ℤ) ≤ ((P (2*j-1)).toNat : ℤ) := by exact_mod_cast hk2
    have h_toNat : ((P (2*j-1)).toNat : ℤ) = P (2*j-1) := Int.toNat_of_nonneg (by omega)
    rwa [h_toNat] at this
  have hP_pos : 0 < P (2*j-1) := P_strict_pos (2*j-1) (by omega)
  have hQ_pos : 0 < Q (2*j-1) := (PQ_pos (2*j-1)).2
  have hQ_sq : (Q (2*j-1))^2 = 2 * (P (2*j-1))^2 - 1 := by
    have H : 2*j-1 > 0 := by omega
    exact PQ_rel_odd (j) hj
  have h_PQ : P (2*j-1) ≤ Q (2*j-1) := P_le_Q_lem (P (2*j-1)) (Q (2*j-1)) hP_pos hQ_pos hQ_sq
  have H_P2j : P (2*j) = Q (2*j-1) + P (2*j-1) := by
    have H1 : 2*j-1+1 = 2*j := by omega
    have H2 := (PQ_step (2*j-1)).1
    rw [H1] at H2
    exact H2
  have H_ineq : 2 * P (2*j-1) ≤ P (2*j) := by linarith
  have H_sq : 4 * (P (2*j-1))^2 ≤ (P (2*j))^2 := by
    have : (2 * P (2*j-1))^2 ≤ (P (2*j))^2 := by
      have : 0 ≤ 2 * P (2*j-1) := by linarith
      nlinarith
    linarith
  have : 2 * (k:ℤ)^2 ≤ 2 * (P (2*j-1))^2 := by
    have : (k:ℤ)^2 ≤ (P (2*j-1))^2 := by
      have : 0 ≤ (k:ℤ) := by omega
      nlinarith
    linarith
  have : 1 ≤ 2 * (P (2*j-1))^2 := by nlinarith
  linarith
