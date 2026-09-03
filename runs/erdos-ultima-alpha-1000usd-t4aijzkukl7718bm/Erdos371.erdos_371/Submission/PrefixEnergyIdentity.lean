import Submission.LogWindowPrefixMeans

/-! An exact finite prefix-energy identity. Its weighted-correlation
hypothesis is not asserted for the largest-prime-factor sign. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma prefixMean_step_difference (f : ℕ → ℝ) (n : ℕ) :
    (n+1 : ℝ)*(prefixMean (n+1) f-prefixMean n f) = f n-prefixMean n f := by
  have h := prefixMean_step_identity f n
  nlinarith

lemma prefixMean_step_energy (f : ℕ → ℝ) (n : ℕ) :
    2*((f n*prefixMean n f-(prefixMean n f)^2)/(n+1 : ℝ)) =
      (prefixMean (n+1) f)^2-(prefixMean n f)^2-
        (prefixMean (n+1) f-prefixMean n f)^2 := by
  have h := prefixMean_step_difference f n
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  rw [← mul_div_assoc,div_eq_iff hn]
  have hh := congrArg (fun x : ℝ => 2*prefixMean n f*x) h
  nlinarith only [hh]

lemma prefixMean_sum_energy (f : ℕ → ℝ) (N : ℕ) :
    2*(∑ n ∈ range N, (f n*prefixMean n f-(prefixMean n f)^2)/(n+1 : ℝ)) =
      (prefixMean N f)^2-
        ∑ n ∈ range N, (prefixMean (n+1) f-prefixMean n f)^2 := by
  rw [mul_sum]
  simp_rw [prefixMean_step_energy]
  rw [sum_sub_distrib,sum_range_sub (fun n => (prefixMean n f)^2)]
  simp [prefixMean]

lemma prefixMean_step_abs_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (n : ℕ) :
    |prefixMean (n+1) f-prefixMean n f| ≤ 2/(n+1 : ℝ) := by
  have h := prefixMean_step_difference f n
  have hn : 0 < (n+1 : ℝ) := by positivity
  have he : prefixMean (n+1) f-prefixMean n f = (f n-prefixMean n f)/(n+1 : ℝ) := by
    apply (eq_div_iff hn.ne').mpr
    nlinarith
  rw [he,abs_div,abs_of_pos hn]
  exact div_le_div_of_nonneg_right
    ((abs_sub _ _).trans (by linarith [hf n,prefixMean_unit_bound f hf n])) hn.le

lemma prefixMean_step_square_sum_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (N : ℕ) :
    (∑ n ∈ range N, (prefixMean (n+1) f-prefixMean n f)^2) ≤ 8 := by
  have hs (n : ℕ) : (prefixMean (n+1) f-prefixMean n f)^2 ≤
      8/((n+1)*(n+2) : ℝ) := by
    have hb := sq_le_sq₀ (abs_nonneg (prefixMean (n+1) f-prefixMean n f))
      (by positivity : (0 : ℝ) ≤ 2/(n+1 : ℝ)) |>.mpr (prefixMean_step_abs_le f hf n)
    rw [sq_abs] at hb
    apply hb.trans
    have h₁ : 0 < (n+1 : ℝ) := by positivity
    have h₂ : 0 < (n+2 : ℝ) := by positivity
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos h₁) (mul_pos h₁ h₂)).mpr
    nlinarith
  have hsum := sum_le_sum (fun n (_ : n ∈ range N) => hs n)
  have he : (∑ n ∈ range N, 8/((n+1)*(n+2) : ℝ)) = 8*(1-1/(N+1 : ℝ)) := by
    rw [← reciprocal_product_sum, mul_sum]
    apply sum_congr rfl
    intro n _
    ring
  rw [he] at hsum
  apply hsum.trans
  have hh : (0 : ℝ) ≤ 1/(N+1 : ℝ) := by positivity
  linarith

lemma prefixMean_energy_correlation_error (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (N : ℕ) :
    |(∑ n ∈ range N, (f n*prefixMean n f)/(n+1 : ℝ))-
      ∑ n ∈ range N, (prefixMean n f)^2/(n+1 : ℝ)| ≤ 5 := by
  have h := prefixMean_sum_energy f N
  simp_rw [sub_div] at h
  rw [sum_sub_distrib] at h
  have hb := prefixMean_unit_bound f hf N
  have hsq : (prefixMean N f)^2 ≤ 1 := by
    simpa only [sq_abs,one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hb
  have hnn : 0 ≤ ∑ n ∈ range N, (prefixMean (n+1) f-prefixMean n f)^2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hs := prefixMean_step_square_sum_le f hf N
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (prefixMean N f)]

lemma prefixMean_harmonic_energy_error (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (N : ℕ) :
    |harmonicRangeMean (N+1) (fun n => f n*prefixMean n f)-
      harmonicRangeMean (N+1) (fun n => (prefixMean n f)^2)| ≤
        5/(harmonic (N+1) : ℝ) := by
  rw [harmonicRangeMean,harmonicRangeMean,← sub_div,abs_div,
    abs_of_pos (harmonic_real_pos N)]
  exact div_le_div_of_nonneg_right (prefixMean_energy_correlation_error f hf (N+1))
    (harmonic_real_pos N).le

/-- The nontrivial premise is a weighted arithmetic cancellation, not just
zero harmonic mean of f itself. -/
theorem prefixMean_harmonic_square_zero_of_correlation_zero (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1)
    (h : Tendsto (fun N => harmonicRangeMean (N+1) (fun n => f n*prefixMean n f))
      atTop (𝓝 0)) :
    Tendsto (fun N => harmonicRangeMean (N+1) (fun n => (prefixMean n f)^2))
      atTop (𝓝 0) := by
  have he : Tendsto (fun N => harmonicRangeMean (N+1) (fun n => f n*prefixMean n f)-
      harmonicRangeMean (N+1) (fun n => (prefixMean n f)^2)) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ (tendsto_const_nhds.div_atTop harmonic_real_tendsto :
      Tendsto (fun N => (5 : ℝ)/(harmonic (N+1) : ℝ)) atTop (𝓝 0))
    intro N
    simpa only [Real.norm_eq_abs] using prefixMean_harmonic_energy_error f hf N
  simpa only [sub_sub_cancel,sub_zero] using h.sub he

#print axioms prefixMean_sum_energy
#print axioms prefixMean_harmonic_square_zero_of_correlation_zero
end Erdos371.FiniteInformation
