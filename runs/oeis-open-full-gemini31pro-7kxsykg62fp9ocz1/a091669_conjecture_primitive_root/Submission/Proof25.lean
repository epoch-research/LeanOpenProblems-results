import Mathlib
import Submission.Spec
import Submission.Proof22
import Submission.Proof23
import Submission.Proof24
import Submission.Proof20
import Submission.Proof19
import Submission.Proof6

open Nat BigOperators

lemma padicValNat_two_pow (k : ℕ) : padicValNat 2 (2 ^ k) = k := by
  have hpos : 2 ^ k ≠ 0 := by
    have : 2 ^ k > 0 := by positivity
    omega
  have h1 : k ≤ padicValNat 2 (2 ^ k) := (padicValNat_dvd_iff_le hpos).mp (dvd_rfl)
  have h2 : padicValNat 2 (2 ^ k) ≤ k := by
    by_contra hc
    have : padicValNat 2 (2 ^ k) ≥ k + 1 := by omega
    have : 2 ^ (k + 1) ∣ 2 ^ k := (padicValNat_dvd_iff_le hpos).mpr this
    have : 2 ^ (k + 1) ≤ 2 ^ k := Nat.le_of_dvd (by positivity) this
    have : 2 ^ (k + 1) > 2 ^ k := by
      have h2 : 2 > 1 := by omega
      exact Nat.pow_lt_pow_right h2 (by omega)
    omega
  omega

lemma pow_two_ge_add_two (m : ℕ) (hm2 : m ≥ 2) : 2 ^ m ≥ m + 2 := by
  induction m, hm2 using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have : 2 * 2 ^ k ≥ 2 * (k + 2) := Nat.mul_le_mul_left 2 ih
    omega

lemma power_of_two_contradiction (n m : ℕ) (hn2 : n > 2) (hcomp : ¬ n.Prime)
  (hn_eq : n = 2 ^ m)
  (h_dvd : n ∣ a (n - 1) + 2 ^ (n - 2)) : False := by
  have hm2 : m ≥ 2 := by
    by_contra h
    have : m < 2 := by omega
    rcases m with _ | _ | _
    · have : n = 1 := by omega
      omega
    · have : n = 2 := by omega
      omega
    · omega
  have h_pow_m : 2 ^ m ≥ m + 2 := pow_two_ge_add_two m hm2
  have hn1 : n - 1 = 2 ^ m - 1 := by omega
  have h_fact_pos : (n - 1).factorial ≠ 0 := Nat.ne_of_gt (Nat.factorial_pos (n - 1))
  have h_P_pos : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := Nat.ne_of_gt (prod_pos n)
  have h_2_pos : 2 ^ (n - 2) ≠ 0 := by
    have h1 : 2 ^ (n - 2) > 0 := by positivity
    omega
  have h_mul : a (n - 1) * (n - 1).factorial = 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := a_mul_fact n hn2
  have h_a_pos : a (n - 1) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h_mul
    have hp2 : 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) = 0 := h_mul.symm
    cases Nat.mul_eq_zero.mp hp2 with
    | inl h => exact h_2_pos h
    | inr h => exact h_P_pos h
  have h_vp_mul : padicValNat 2 (a (n - 1) * (n - 1).factorial) = padicValNat 2 (a (n - 1)) + padicValNat 2 (n - 1).factorial := padicValNat.mul h_a_pos h_fact_pos
  have h_vp_RHS : padicValNat 2 (2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) = padicValNat 2 (2 ^ (n - 2)) + padicValNat 2 ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := padicValNat.mul h_2_pos h_P_pos
  have h_vp_P : padicValNat 2 ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) = 0 := padicValNat_P_two n hn2
  have h_vp_2 : padicValNat 2 (2 ^ (n - 2)) = n - 2 := padicValNat_two_pow (n - 2)
  have h_vp_fact : padicValNat 2 (n - 1).factorial = n - 1 - m := by
    have h1 : padicValNat 2 (n - 1).factorial = (n - 1) - (Nat.digits 2 (n - 1)).sum := by
      have h_sub : (2 - 1) * padicValNat 2 (n - 1).factorial = (n - 1) - (Nat.digits 2 (n - 1)).sum := sub_one_mul_padicValNat_factorial (n - 1)
      have h_sub2 : 2 - 1 = 1 := rfl
      rw [h_sub2, one_mul] at h_sub
      exact h_sub
    have h2 : (Nat.digits 2 (n - 1)).sum = m := by
      rw [hn1]
      exact digits_two_pow_sub_one m
    rw [h2] at h1
    exact h1
  have h_vp_a : padicValNat 2 (a (n - 1)) = m - 1 := by
    have h_eq1 : padicValNat 2 (a (n - 1)) + padicValNat 2 (n - 1).factorial = padicValNat 2 (2 ^ (n - 2)) + padicValNat 2 ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
      rw [← h_vp_mul, h_mul, h_vp_RHS]
    rw [h_vp_fact, h_vp_P, h_vp_2, add_zero] at h_eq1
    have : n ≥ m + 2 := by
      have : n = 2 ^ m := hn_eq
      omega
    omega
  have h_n_dvd_sum : 2 ^ m ∣ 2 ^ (n - 2) + a (n - 1) := by
    have : 2 ^ m ∣ a (n - 1) + 2 ^ (n - 2) := by
      rw [← hn_eq]
      exact h_dvd
    rw [add_comm] at this
    exact this
  have h_n_dvd_2 : 2 ^ m ∣ 2 ^ (n - 2) := by
    have hpow : m ≤ n - 2 := by
      have : n ≥ m + 2 := by
        have : n = 2 ^ m := hn_eq
        omega
      omega
    exact Nat.pow_dvd_pow 2 hpow
  have h_n_dvd_a : 2 ^ m ∣ a (n - 1) := (Nat.dvd_add_right h_n_dvd_2).mp h_n_dvd_sum
  have h_dvd_a : m ≤ padicValNat 2 (a (n - 1)) := (padicValNat_dvd_iff_le h_a_pos).mp h_n_dvd_a
  omega
