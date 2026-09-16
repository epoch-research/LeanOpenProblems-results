import Mathlib
import Submission.Spec
import Submission.Proof17
import Submission.Proof13
import Submission.Proof7
import Submission.Proof19

open Nat BigOperators

lemma exact_div (n : ℕ) (hn : n > 2) :
  (n - 1).factorial ∣ 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p m hp hpm
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hodd : p > 2
  · have h_fact_pos : (n - 1).factorial ≠ 0 := by
      exact Nat.ne_of_gt (Nat.factorial_pos (n - 1))
    have h1 : m ≤ padicValNat p (n - 1).factorial := (padicValNat_dvd_iff_le h_fact_pos).mp hpm
    have h2 : padicValNat p (n - 1).factorial ≤ (n - 2) / (p - 1) := vp_fact_le n p hn
    have h3 : (n - 2) / (p - 1) ≤ padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := vp_P_lower_bound n p hn hodd
    have h4 : m ≤ padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by omega
    have hprod_pos : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by
      exact Nat.ne_of_gt (prod_pos n)
    have h5 : p ^ m ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := (padicValNat_dvd_iff_le hprod_pos).mpr h4
    exact dvd_mul_of_dvd_right h5 _
  · have hp_ge2 : p ≥ 2 := hp.two_le
    have p2 : p = 2 := by omega
    subst p2
    have h_fact_pos : (n - 1).factorial ≠ 0 := by
      exact Nat.ne_of_gt (Nat.factorial_pos (n - 1))
    have h1 : m ≤ padicValNat 2 (n - 1).factorial := (padicValNat_dvd_iff_le h_fact_pos).mp hpm
    have h2 : padicValNat 2 (n - 1).factorial ≤ n - 2 := by
      have hle : padicValNat 2 (n - 1).factorial ≤ (n - 2) / (2 - 1) := vp_fact_le n 2 hn
      omega
    have h3 : m ≤ n - 2 := by omega
    have h4 : 2 ^ m ∣ 2 ^ (n - 2) := Nat.pow_dvd_pow 2 h3
    exact dvd_mul_of_dvd_left h4 _
