import FormalConjecturesUtil

/-!
# The natural-cutoff average of the divisor function

The divisor summatory function is bounded between `N * harmonic N - N` and
`N * harmonic N`. The Euler–Mascheroni asymptotic for the harmonic numbers
then gives its asymptotic `N * log N`, with the cutoff taken in `ℕ`.

This module supplies a supporting lemma, not a theorem about divisor sums
along arbitrary polynomial values.
-/

/-- The divisor-counting arithmetic function, called `sigma 0` in mathlib. -/
abbrev ArithmeticFunction.sigma0 : ArithmeticFunction ℕ := ArithmeticFunction.sigma 0

namespace Erdos975Support

open Filter
open scoped Topology

/-- The sum of the number of divisors over the natural numbers at most `N`. -/
noncomputable def divisorSummatory (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Iic N, (ArithmeticFunction.sigma0 n : ℝ)

/-- Counting divisor pairs expresses the summatory function as a sum of natural quotients. -/
theorem divisorSummatory_eq_sum_div (N : ℕ) :
    divisorSummatory N = ∑ n ∈ Finset.Ioc 0 N, ((N / n : ℕ) : ℝ) := by
  calc
    divisorSummatory N =
        ∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.sigma0 n : ℝ) := by
      unfold divisorSummatory
      symm
      apply Finset.sum_subset Finset.Ioc_subset_Iic_self
      intro n hn hn'
      have hnN : n ≤ N := Finset.mem_Iic.mp hn
      have hn0 : n = 0 := by
        simp only [Finset.mem_Ioc] at hn'
        omega
      subst n
      simp [ArithmeticFunction.sigma0]
    _ = ∑ n ∈ Finset.Ioc 0 N, ((N / n : ℕ) : ℝ) := by
      exact_mod_cast ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div N

/-- Harmonic numbers as a real sum on the same interval as the divisor identity. -/
lemma harmonic_eq_sum_Ioc (N : ℕ) :
    (harmonic N : ℝ) = ∑ n ∈ Finset.Ioc 0 N, (n : ℝ)⁻¹ := by
  have hI : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [harmonic_eq_sum_Icc, hI]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

lemma sum_div_eq_mul_harmonic (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (N : ℝ) / (n : ℝ)) =
      (N : ℝ) * (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Ioc, Finset.mul_sum]
  simp only [div_eq_mul_inv]

/-- Each natural quotient is at most the corresponding real quotient. -/
theorem divisorSummatory_upper_bound (N : ℕ) :
    divisorSummatory N ≤ (N : ℝ) * (harmonic N : ℝ) := by
  rw [divisorSummatory_eq_sum_div, ← sum_div_eq_mul_harmonic]
  exact Finset.sum_le_sum fun n _ ↦ Nat.cast_div_le

/-- Each natural quotient loses at most one from the corresponding real quotient. -/
theorem divisorSummatory_lower_bound (N : ℕ) :
    (N : ℝ) * (harmonic N : ℝ) - N ≤ divisorSummatory N := by
  rw [divisorSummatory_eq_sum_div]
  have hfloor (n : ℕ) : (N : ℝ) / (n : ℝ) - 1 ≤ ((N / n : ℕ) : ℝ) := by
    simpa only [Nat.floor_div_eq_div] using
      (Nat.sub_one_lt_floor ((N : ℝ) / (n : ℝ))).le
  calc
    (N : ℝ) * (harmonic N : ℝ) - N =
        ∑ n ∈ Finset.Ioc 0 N, ((N : ℝ) / (n : ℝ) - 1) := by
      rw [Finset.sum_sub_distrib, sum_div_eq_mul_harmonic]
      simp
    _ ≤ ∑ n ∈ Finset.Ioc 0 N, ((N / n : ℕ) : ℝ) :=
      Finset.sum_le_sum fun n _ ↦ hfloor n

/-- The nonnegative floor-sum error is at most `N`. -/
theorem divisorSummatory_error_bounds (N : ℕ) :
    0 ≤ (N : ℝ) * (harmonic N : ℝ) - divisorSummatory N ∧
      (N : ℝ) * (harmonic N : ℝ) - divisorSummatory N ≤ N := by
  constructor
  · exact sub_nonneg.mpr (divisorSummatory_upper_bound N)
  · linarith [divisorSummatory_lower_bound N]

/-- After normalization by `N * log N`, the error is at most `1 / log N`. -/
theorem divisorSummatory_normalized_error_bounds {N : ℕ} (hN : 2 ≤ N) :
    0 ≤ ((N : ℝ) * (harmonic N : ℝ) - divisorSummatory N) /
        ((N : ℝ) * Real.log (N : ℝ)) ∧
      ((N : ℝ) * (harmonic N : ℝ) - divisorSummatory N) /
        ((N : ℝ) * Real.log (N : ℝ)) ≤ 1 / Real.log (N : ℝ) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hNpos : 0 < (N : ℝ) := lt_trans zero_lt_one hN1
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hden : 0 < (N : ℝ) * Real.log (N : ℝ) := mul_pos hNpos hlog
  constructor
  · exact div_nonneg (divisorSummatory_error_bounds N).1 hden.le
  · calc
      ((N : ℝ) * (harmonic N : ℝ) - divisorSummatory N) /
          ((N : ℝ) * Real.log (N : ℝ)) ≤
          (N : ℝ) / ((N : ℝ) * Real.log (N : ℝ)) :=
        div_le_div_of_nonneg_right (divisorSummatory_error_bounds N).2 hden.le
      _ = 1 / Real.log (N : ℝ) := by
        rw [div_mul_cancel_left₀ hNpos.ne', one_div]

lemma tendsto_log_nat_atTop :
    Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_one_div_log_nat :
    Tendsto (fun N : ℕ ↦ 1 / Real.log (N : ℝ)) atTop (𝓝 (0 : ℝ)) :=
  tendsto_log_nat_atTop.const_div_atTop 1

/-- Euler–Mascheroni convergence implies that `harmonic N / log N` tends to one. -/
theorem tendsto_harmonic_div_log_nat :
    Tendsto (fun N : ℕ ↦ (harmonic N : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
  have hsmall := Real.tendsto_harmonic_sub_log.div_atTop tendsto_log_nat_atTop
  have h : Tendsto (fun N : ℕ ↦
      (1 : ℝ) + ((harmonic N : ℝ) - Real.log (N : ℝ)) / Real.log (N : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hsmall
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog0 : Real.log (N : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  rw [sub_div, div_self hlog0]
  ring

/-- The floor-sum error vanishes after division by `N * log N`. -/
theorem tendsto_divisorSummatory_normalized_error :
    Tendsto (fun N : ℕ ↦
      ((N : ℝ) * (harmonic N : ℝ) - divisorSummatory N) /
        ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 (0 : ℝ)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds tendsto_one_div_log_nat
  · filter_upwards [eventually_ge_atTop 2] with N hN using
      (divisorSummatory_normalized_error_bounds hN).1
  · filter_upwards [eventually_ge_atTop 2] with N hN using
      (divisorSummatory_normalized_error_bounds hN).2

/-- The classical summatory divisor asymptotic, with a natural-number cutoff. -/
theorem tendsto_divisorSummatory_div_mul_log :
    Tendsto (fun N : ℕ ↦
      divisorSummatory N / ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 (1 : ℝ)) := by
  have h : Tendsto (fun N : ℕ ↦
      (harmonic N : ℝ) / Real.log (N : ℝ) -
        ((N : ℝ) * (harmonic N : ℝ) - divisorSummatory N) /
          ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using
      tendsto_harmonic_div_log_nat.sub tendsto_divisorSummatory_normalized_error
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < N by omega))
  rw [← mul_div_mul_left (harmonic N : ℝ) (Real.log (N : ℝ)) hN0, ← sub_div]
  congr 1
  ring

end Erdos975Support
