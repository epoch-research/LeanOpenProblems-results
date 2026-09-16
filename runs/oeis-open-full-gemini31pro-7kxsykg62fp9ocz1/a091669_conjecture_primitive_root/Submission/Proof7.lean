import Mathlib
import Submission.Spec
import Submission.Proof6

open Nat BigOperators

lemma vp_fact_upper_bound (n p : ℕ) [Fact p.Prime] (hn2 : n > 2) (hodd : p > 2) (hcomp : ¬ n.Prime) (hdvd : p ∣ n) :
  padicValNat p (n - 1).factorial < (n - 2) / (p - 1) := by
  have h1 : (p - 1) * padicValNat p (n - 1).factorial = (n - 1) - (p.digits (n - 1)).sum := by
    exact sub_one_mul_padicValNat_factorial (n - 1)
  have h2 : (p.digits (n - 1)).sum ≥ p := digits_sum_ge_p n p hn2 hcomp hdvd
  have hk : ∃ k, n = k * p := exists_eq_mul_left_of_dvd hdvd
  rcases hk with ⟨k, rfl⟩
  have hk2 : k ≥ 2 := by
    by_contra h
    have h1 : k < 2 := by omega
    rcases k with _ | _ | _
    · omega
    · have : 1 * p = p := one_mul p
      rw [this] at hcomp
      exact hcomp (Fact.out)
    · omega
  have hp2 : p ≥ 3 := by omega
  have h3 : (p - 1) * padicValNat p (k * p - 1).factorial ≤ k * p - 1 - p := by omega
  have h6 : (padicValNat p (k * p - 1).factorial + 1) * (p - 1) ≤ k * p - 2 := by
    have eq1 : (padicValNat p (k * p - 1).factorial + 1) * (p - 1) = (p - 1) * padicValNat p (k * p - 1).factorial + (p - 1) := by ring
    rw [eq1]
    have eq2 : k * p - 1 - p + (p - 1) = k * p - 2 := by
      have h_k_p : k * p ≥ 2 * p := by nlinarith
      have h_sub : k * p - 1 ≥ p := by omega
      have h_kp_pos : k * p ≥ 1 := by omega
      have h_kp_2 : k * p ≥ 2 := by omega
      zify [h_k_p, h_sub, h_kp_pos, h_kp_2, show p ≥ 1 by omega]
      ring
    omega
  have h7 : padicValNat p (k * p - 1).factorial + 1 ≤ (k * p - 2) / (p - 1) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    exact h6
  omega
