import Mathlib
import Submission.Spec
import Submission.Helper9
import Submission.Helper10
import Submission.Helper11
import Submission.Helper12

open Nat Real intervalIntegral Polynomial Filter Topology Set

lemma k_I_k_tendsto_zero : Tendsto (fun k : ℕ => (k : ℝ) * I_k k) atTop (nhds 0) := by
  have H_le : ∀ k : ℕ, 0 ≤ (k : ℝ) * I_k k := by
    intro k
    have h1 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have h2 : 0 ≤ I_k k := I_k_nonneg k
    positivity
  have H_bound : ∀ k : ℕ, (k : ℝ) * I_k k ≤ (exp 1) * ((k : ℝ) * ((k.factorial : ℝ)⁻¹)) := by
    intro k
    have h_ik_le : I_k k ≤ exp 1 * ((k.factorial : ℝ)⁻¹) := I_k_le k
    have h_k_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    calc
      (k : ℝ) * I_k k ≤ (k : ℝ) * (exp 1 * ((k.factorial : ℝ)⁻¹)) := mul_le_mul_of_nonneg_left h_ik_le h_k_nonneg
      _ = (exp 1) * ((k : ℝ) * ((k.factorial : ℝ)⁻¹)) := by ring
  have h1 : Tendsto (fun k : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
  have h2 : Tendsto (fun k : ℕ => (exp 1) * ((k : ℝ) * ((k.factorial : ℝ)⁻¹))) atTop (nhds 0) := by
    have ht := k_div_fact_tendsto_zero
    have H2 := Tendsto.const_mul (exp 1) ht
    have hc : exp 1 * 0 = 0 := mul_zero (exp 1)
    rw [hc] at H2
    exact H2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le h1 h2 H_le H_bound

lemma J_odd_term_tendsto_zero : Tendsto (fun k : ℕ => (2 * (k:ℝ) + 1) * J (2 * k - 1)) atTop (nhds 0) := by
  have eq1 : (fun k : ℕ => (2 * (k:ℝ) + 1) * J (2 * k - 1)) =ᶠ[atTop] (fun k : ℕ => (2 * (k:ℝ) + 1) * ((-1 : ℝ) ^ (k - 1) * I_k k)) := by
    apply eventually_atTop.mpr
    use 1
    intro k hk
    dsimp
    have eq_idx : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
    rw [eq_idx, J_odd_eq_I (k - 1)]
    congr 1
    have eq_k : k - 1 + 1 = k := by omega
    rw [eq_k]
  have H2 : Tendsto (fun k : ℕ => (2 * (k:ℝ) + 1) * ((-1 : ℝ) ^ (k - 1) * I_k k)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have eq_norm : (fun k : ℕ => ‖(2 * (k:ℝ) + 1) * ((-1 : ℝ) ^ (k - 1) * I_k k)‖) = (fun k : ℕ => (2 * (k:ℝ) + 1) * ‖I_k k‖) := by
      ext k
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      have : 0 ≤ 2 * (k:ℝ) + 1 := by positivity
      rw [norm_of_nonneg this]
    rw [eq_norm]
    have eq_split : (fun k : ℕ => (2 * (k:ℝ) + 1) * ‖I_k k‖) = (fun k : ℕ => 2 * ((k:ℝ) * I_k k) + I_k k) := by
      ext k
      have : 0 ≤ I_k k := I_k_nonneg k
      rw [norm_of_nonneg this]
      ring
    rw [eq_split]
    have t1 : Tendsto (fun k : ℕ => 2 * ((k:ℝ) * I_k k)) atTop (nhds 0) := by
      have h := Tendsto.const_mul 2 k_I_k_tendsto_zero
      rw [mul_zero] at h
      exact h
    have t2 : Tendsto (fun k : ℕ => I_k k) atTop (nhds 0) := I_k_tendsto_zero
    have h_add := Tendsto.add t1 t2
    rw [add_zero] at h_add
    exact h_add
  exact Tendsto.congr' eq1.symm H2

