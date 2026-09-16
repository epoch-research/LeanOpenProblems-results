import Mathlib
open Nat Real Filter Topology Set

lemma k_div_fact_tendsto_zero : Tendsto (fun k : ℕ => (k : ℝ) * ((k.factorial : ℝ)⁻¹)) atTop (nhds 0) := by
  have H1 : (fun k : ℕ => (k : ℝ) * ((k.factorial : ℝ)⁻¹)) =ᶠ[atTop] (fun k : ℕ => (((k - 1).factorial : ℝ)⁻¹)) := by
    apply eventually_atTop.mpr
    use 1
    intro k hk
    have eq1 : k.factorial = k * (k - 1).factorial := Nat.mul_factorial_pred (by omega) |>.symm
    dsimp
    have eq2 : (k.factorial : ℝ) = (k : ℝ) * ((k - 1).factorial : ℝ) := by exact_mod_cast eq1
    rw [eq2]
    rw [mul_inv]
    have h_k_ne_zero : (k : ℝ) ≠ 0 := by
      have : (k:ℝ) ≥ 1 := by exact_mod_cast hk
      linarith
    calc
      (k : ℝ) * ((k : ℝ)⁻¹ * ((k - 1).factorial : ℝ)⁻¹) = ((k : ℝ) * (k : ℝ)⁻¹) * ((k - 1).factorial : ℝ)⁻¹ := by ring
      _ = 1 * ((k - 1).factorial : ℝ)⁻¹ := by rw [mul_inv_cancel₀ h_k_ne_zero]
      _ = ((k - 1).factorial : ℝ)⁻¹ := by ring
  have ht : Tendsto (fun k : ℕ => (((k - 1).factorial : ℝ)⁻¹)) atTop (nhds 0) := by
    have H := FloorSemiring.tendsto_pow_div_factorial_atTop (1 : ℝ)
    simp only [one_pow, one_div] at H
    have H_sub : Tendsto (fun k : ℕ => k - 1) atTop atTop := tendsto_sub_atTop_nat 1
    exact H.comp H_sub
  exact Tendsto.congr' H1.symm ht
