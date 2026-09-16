import Mathlib
import Submission.Spec
import Submission.Proof22
import Submission.Proof21
import Submission.Proof20
import Submission.Proof13
import Submission.Proof7
import Submission.Proof19

open Nat BigOperators

lemma odd_prime_factor_contradiction (n p : ℕ) (hn2 : n > 2) (hcomp : ¬ n.Prime)
  (hp_prime : p.Prime) (hp_odd : p > 2) (hp_dvd_n : p ∣ n)
  (h_dvd : n ∣ a (n - 1) + 2 ^ (n - 2)) : False := by
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have h_fact_pos : (n - 1).factorial ≠ 0 := Nat.ne_of_gt (Nat.factorial_pos (n - 1))
  have h_mul : a (n - 1) * (n - 1).factorial = 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := a_mul_fact n hn2
  have h_vp_fact : padicValNat p (n - 1).factorial < (n - 2) / (p - 1) := vp_fact_upper_bound n p hn2 hp_odd hcomp hp_dvd_n
  have h_vp_P : (n - 2) / (p - 1) ≤ padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := vp_P_lower_bound n p hn2 hp_odd
  have h_vp_P_gt : padicValNat p (n - 1).factorial < padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by omega
  have h_P_pos : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := Nat.ne_of_gt (prod_pos n)
  have h_2_pos : 2 ^ (n - 2) ≠ 0 := by
    have h1 : 2 ^ (n - 2) > 0 := by positivity
    omega
  have h_a_pos : a (n - 1) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h_mul
    have hp2 : 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) = 0 := h_mul.symm
    cases Nat.mul_eq_zero.mp hp2 with
    | inl h => exact h_2_pos h
    | inr h => exact h_P_pos h
  have h_vp_mul : padicValNat p (a (n - 1) * (n - 1).factorial) = padicValNat p (a (n - 1)) + padicValNat p (n - 1).factorial := padicValNat.mul h_a_pos h_fact_pos
  have h_vp_RHS : padicValNat p (2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) = padicValNat p (2 ^ (n - 2)) + padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := padicValNat.mul h_2_pos h_P_pos
  have h_vp_2 : padicValNat p (2 ^ (n - 2)) = 0 := by
    by_contra hz
    have h1 : padicValNat p (2 ^ (n - 2)) ≥ 1 := by omega
    have h2 : p ^ 1 ∣ 2 ^ (n - 2) := (padicValNat_dvd_iff_le h_2_pos).mpr h1
    have h3 : p ∣ 2 ^ (n - 2) := by
      have : p ^ 1 = p := pow_one p
      rw [← this]
      exact h2
    have h4 : p ∣ 2 := hp_prime.dvd_of_dvd_pow h3
    have h5 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp h4
    omega
  have h_eq : padicValNat p (a (n - 1)) + padicValNat p (n - 1).factorial = padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
    rw [← h_vp_mul, h_mul, h_vp_RHS, h_vp_2, zero_add]
  have h_vp_a : padicValNat p (a (n - 1)) ≥ 1 := by omega
  have h_dvd_a : p ∣ a (n - 1) := by
    have hdvd1 : p ^ 1 ∣ a (n - 1) := (padicValNat_dvd_iff_le h_a_pos).mpr h_vp_a
    have hpow : p ^ 1 = p := pow_one p
    rw [← hpow]
    exact hdvd1
  have h_p_dvd_sum : p ∣ a (n - 1) + 2 ^ (n - 2) := Nat.dvd_trans hp_dvd_n h_dvd
  have h_p_dvd_2 : p ∣ 2 ^ (n - 2) := (Nat.dvd_add_right h_dvd_a).mp h_p_dvd_sum
  have h_p_dvd_2' : p ∣ 2 := hp_prime.dvd_of_dvd_pow h_p_dvd_2
  have h_p_eq_2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp h_p_dvd_2'
  omega
