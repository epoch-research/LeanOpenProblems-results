import Mathlib
import Submission.Spec
import Submission.Helper9
import Submission.Helper10

open Nat Real intervalIntegral Polynomial Filter Topology Set

lemma I_k_tendsto_zero : Tendsto I_k atTop (nhds 0) := by
  have h1 : Tendsto (fun k : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
  have h2 : Tendsto (fun k : ℕ => exp 1 * ((k.factorial : ℝ)⁻¹)) atTop (nhds 0) := by
    have ht : Tendsto (fun k : ℕ => ((k.factorial : ℝ)⁻¹)) atTop (nhds 0) := by
      have H := FloorSemiring.tendsto_pow_div_factorial_atTop (1 : ℝ)
      simp only [one_pow, one_div] at H
      exact H
    have H2 := Tendsto.const_mul (exp 1) ht
    have hc : exp 1 * 0 = 0 := mul_zero (exp 1)
    rw [hc] at H2
    exact H2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le h1 h2
  · intro k
    exact I_k_nonneg k
  · intro k
    exact I_k_le k

lemma J_odd_tendsto_zero : Tendsto (fun k => J (2 * k + 1)) atTop (nhds 0) := by
  have ht : Tendsto (fun k => (-1 : ℝ) ^ k * I_k (k + 1)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have H : (fun k => ‖(-1 : ℝ) ^ k * I_k (k + 1)‖) = (fun k => ‖I_k (k + 1)‖) := by
      ext k
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [H]
    apply tendsto_zero_iff_norm_tendsto_zero.mp
    have H2 : Tendsto (fun k => I_k (k + 1)) atTop (nhds 0) := by
      exact I_k_tendsto_zero.comp (tendsto_add_atTop_nat 1)
    exact H2
  have eq : (fun k => J (2 * k + 1)) = (fun k => (-1 : ℝ) ^ k * I_k (k + 1)) := by
    ext k
    exact J_odd_eq_I k
  rw [eq]
  exact ht
