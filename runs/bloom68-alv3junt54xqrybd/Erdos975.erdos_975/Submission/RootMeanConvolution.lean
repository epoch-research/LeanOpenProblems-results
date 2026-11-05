import Submission.RootMeanPeriodic

/-!
# Linear means under absolutely summable Dirichlet convolution

If `A(N)/N → κ`, `A(0) = 0`, and `∑ |b(d)|/d < ∞`, then
`(∑_{1 ≤ d ≤ N} b(d) A(⌊N/d⌋))/N → κ ∑ b(d)/d`.
This is proved by Tannery's dominated convergence theorem, with the global
linear bound on `A` derived from its convergence, not assumed separately.

The arithmetic-function version uses Mathlib's exact finite convolution
summatory identity. These are general analytic transfer lemmas. They do not
assume or assert an Euler correction for polynomial root counts.
-/

namespace Erdos975Support

open Filter
open scoped Topology

/-- A convergent normalized sequence, vanishing at zero, has a global
linear norm bound. -/
theorem exists_linear_norm_bound_of_tendsto {A : ℕ → ℝ} {κ : ℝ}
    (hA0 : A 0 = 0)
    (hA : Tendsto (fun N : ℕ ↦ A N / (N : ℝ)) atTop (𝓝 κ)) :
    ∃ C ≥ (0 : ℝ), ∀ N : ℕ, ‖A N‖ ≤ C * (N : ℝ) := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hA).exists_norm_le
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ (Set.mem_range_self 0))
  refine ⟨C, hC0, ?_⟩
  intro N
  by_cases hN : N = 0
  · simp [hN, hA0]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  calc
    ‖A N‖ = ‖A N / (N : ℝ)‖ * (N : ℝ) := by
      rw [norm_div, Real.norm_natCast, div_mul_cancel₀ _ hN0]
    _ ≤ C * (N : ℝ) := mul_le_mul_of_nonneg_right
      (hC _ (Set.mem_range_self N)) (Nat.cast_nonneg N)

/-- A fixed quotient cutoff changes the limiting normalization by `1/d`. -/
theorem tendsto_quotientCutoff_div {A : ℕ → ℝ} {κ : ℝ}
    (hA : Tendsto (fun N : ℕ ↦ A N / (N : ℝ)) atTop (𝓝 κ))
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ ↦ A (N / d) / (N : ℝ)) atTop (𝓝 (κ / (d : ℝ))) := by
  have ht := (hA.comp (Nat.tendsto_div_const_atTop hd.ne')).mul (tendsto_natDiv_div d hd)
  simp only [Function.comp_apply, mul_one_div] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop d] with N hN
  have hm : 0 < N / d := Nat.div_pos hN hd
  have hm0 : ((N / d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  exact div_mul_div_cancel₀ hm0

/-- The coefficient-level convolution mean theorem. Its hypotheses are
explicitly analytic: no polynomial Euler factorization is hidden here. -/
theorem tendsto_normalized_quotient_sum {A b : ℕ → ℝ} {κ : ℝ}
    (hA0 : A 0 = 0)
    (hA : Tendsto (fun N : ℕ ↦ A N / (N : ℝ)) atTop (𝓝 κ))
    (hb : Summable (fun d : ℕ ↦ ‖b d / (d : ℝ)‖)) :
    Tendsto (fun N : ℕ ↦
      (∑ d ∈ Finset.Ioc 0 N, b d * A (N / d)) / (N : ℝ)) atTop
      (𝓝 (κ * ∑' d : ℕ, b d / (d : ℝ))) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_linear_norm_bound_of_tendsto hA0 hA
  let F : ℕ → ℕ → ℝ := fun N d ↦ b d * A (N / d) / (N : ℝ)
  have hpoint (d : ℕ) : Tendsto (fun N ↦ F N d) atTop (𝓝 (κ * (b d / (d : ℝ)))) := by
    by_cases hd : d = 0
    · simp only [F, hd, Nat.div_zero, hA0, mul_zero, zero_div, Nat.cast_zero, div_zero]
      exact tendsto_const_nhds
    have ht := (tendsto_quotientCutoff_div hA d (Nat.pos_of_ne_zero hd)).const_mul (b d)
    convert ht using 1
    · funext N
      dsimp only [F]
      ring
    · congr 1
      ring
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ d : ℕ, ‖F N d‖ ≤ C * ‖b d / (d : ℝ)‖ := by
    filter_upwards [eventually_ge_atTop 1] with N hN d
    by_cases hd : d = 0
    · simp [F, hd, hA0]
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
    dsimp only [F]
    rw [norm_div, norm_mul, Real.norm_natCast]
    calc
      ‖b d‖ * ‖A (N / d)‖ / (N : ℝ) ≤
          ‖b d‖ * (C * ((N / d : ℕ) : ℝ)) / (N : ℝ) := by
        gcongr
        exact hC (N / d)
      _ ≤ ‖b d‖ * (C * ((N : ℝ) / (d : ℝ))) / (N : ℝ) := by
        gcongr
        exact Nat.cast_div_le
      _ = C * ‖b d / (d : ℝ)‖ := by
        rw [norm_div, Real.norm_natCast]
        field_simp
  have ht := tendsto_tsum_of_dominated_convergence (hb.mul_left C) hpoint hbound
  rw [tsum_mul_left] at ht
  have hfinite (N : ℕ) : (∑' d : ℕ, F N d) =
      ∑ d ∈ Finset.Ioc 0 N, F N d := by
    apply tsum_eq_sum
    intro d hd
    have hcase : d = 0 ∨ N < d := by
      simp only [Finset.mem_Ioc, not_and_or, not_lt, not_le] at hd
      omega
    rcases hcase with rfl | hdN
    · simp [F, hA0]
    · simp [F, Nat.div_eq_of_lt hdN, hA0]
  apply ht.congr
  intro N
  rw [hfinite, Finset.sum_div]

/-- Positive-cutoff summation of a real arithmetic function. -/
noncomputable def arithmeticSummatory (a : ArithmeticFunction ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 N, a n

@[simp]
theorem arithmeticSummatory_zero (a : ArithmeticFunction ℝ) : arithmeticSummatory a 0 = 0 := by
  simp [arithmeticSummatory]

/-- Dirichlet convolution preserves a linear mean when the second coefficient
sequence is absolutely summable with weight `1/d`. -/
theorem tendsto_summatory_dirichletConvolution (a b : ArithmeticFunction ℝ) {κ : ℝ}
    (ha : Tendsto (fun N : ℕ ↦ arithmeticSummatory a N / (N : ℝ)) atTop (𝓝 κ))
    (hb : Summable (fun d : ℕ ↦ ‖b d / (d : ℝ)‖)) :
    Tendsto (fun N : ℕ ↦ arithmeticSummatory (a * b) N / (N : ℝ)) atTop
      (𝓝 (κ * ∑' d : ℕ, b d / (d : ℝ))) := by
  have ht := tendsto_normalized_quotient_sum (arithmeticSummatory_zero a) ha hb
  apply ht.congr
  intro N
  rw [arithmeticSummatory, mul_comm a b, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  rfl

end Erdos975Support
