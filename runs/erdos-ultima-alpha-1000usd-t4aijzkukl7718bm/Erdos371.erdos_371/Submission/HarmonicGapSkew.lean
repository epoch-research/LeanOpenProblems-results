import Submission.SmoothCutoffSkew

/-! A uniform signed estimate with harmonic weights over all positive gaps.
The estimate is a finite Hilbert inequality proved using the first Bernoulli
polynomial. It does not assert cancellation at the fixed gap one. -/

namespace Erdos371
namespace HarmonicGap
open Finset MeasureTheory Complex
open scoped Real ComplexConjugate

noncomputable def monomial (i : ℤ) (x : ℝ) : ℂ := fourier i (x : UnitAddCircle)

@[fun_prop] lemma continuous_monomial (i : ℤ) : Continuous (monomial i) := by
  unfold monomial
  simp only [fourier_coe_apply]
  fun_prop

lemma monomial_orthogonality (i j : ℤ) :
    (∫ x in (0 : ℝ)..1, monomial j x * conj (monomial i x)) =
      if i = j then (1 : ℂ) else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T := 1))) i j
  rw [ContinuousMap.inner_toLp, AddCircle.integral_haarAddCircle] at h
  norm_num only [inv_one, one_smul] at h
  rw [← AddCircle.intervalIntegral_preimage 1 0] at h
  simpa only [zero_add, monomial] using h

lemma monomial_bernoulli_integral (i j : ℤ) :
    (2 * (Real.pi : ℂ) * I) *
        (∫ x in (0 : ℝ)..1, (x - 1/2 : ℝ) *
          (monomial j x * conj (monomial i x))) =
      1 / ((j : ℂ) - i) := by
  have h := bernoulliFourierCoeff_eq (k := 1) (by decide) (i-j)
  simp only [bernoulliFourierCoeff, fourierCoeffOn_eq_integral,
    sub_zero, div_one, one_smul, bernoulliFun_one, Nat.factorial_one,
    Nat.cast_one, pow_one, smul_eq_mul] at h
  have he (x : ℝ) :
      (x - 1/2 : ℝ) * (monomial j x * conj (monomial i x)) =
        fourier (-(i-j)) (x : UnitAddCircle) * (x - 1/2 : ℝ) := by
    simp only [monomial, ← fourier_neg, ← fourier_add]
    rw [mul_comm]
    rw [show j + -i = -(i-j) by omega]
  simp_rw [he]
  simp only [fourier_coe_apply, sub_zero] at h ⊢
  rw [h]
  have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  push_cast
  rw [show (2 : ℂ)*Real.pi*I*((i : ℂ)-j) =
    -(2*Real.pi*I*((j : ℂ)-i)) by ring]
  simp only [div_neg, neg_div, neg_neg]
  simpa only [mul_one, one_mul, one_div, div_eq_mul_inv] using (mul_div_mul_left (1 : ℂ) ((j : ℂ)-i) hpi)

noncomputable def polynomial (a : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ i ∈ range N, (a i : ℂ) * monomial i x

@[fun_prop] lemma continuous_polynomial (a : ℕ → ℝ) (N : ℕ) : Continuous (polynomial a N) := by
  unfold polynomial
  exact continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_monomial i)

lemma polynomial_product (a b : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    polynomial b N x * conj (polynomial a N x) =
      ∑ i ∈ range N, ∑ j ∈ range N,
        ((a i * b j : ℝ) : ℂ) * (monomial j x * conj (monomial i x)) := by
  unfold polynomial
  simp only [map_sum, map_mul, conj_ofReal, mul_sum, sum_mul, ofReal_mul]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

lemma polynomial_parseval_complex (a : ℕ → ℝ) (N : ℕ) :
    (∫ x in (0 : ℝ)..1, polynomial a N x * conj (polynomial a N x)) =
      ((∑ i ∈ range N, (a i)^2 : ℝ) : ℂ) := by
  simp_rw [polynomial_product]
  have hc (i j : ℕ) : Continuous (fun x : ℝ =>
      ((a i * a j : ℝ) : ℂ) * (monomial j x * conj (monomial i x))) := by
    fun_prop
  rw [intervalIntegral.integral_finset_sum (fun i _ =>
    (continuous_finset_sum (range N) fun j _ => hc i j).intervalIntegrable 0 1)]
  simp_rw [intervalIntegral.integral_finset_sum (fun j _ => (hc _ j).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, monomial_orthogonality]
  simp only [mul_ite, mul_one, mul_zero, Int.natCast_inj, Complex.ofReal_sum]
  apply sum_congr rfl
  intro i hi
  simp [hi, sq]

lemma polynomial_parseval (a : ℕ → ℝ) (N : ℕ) :
    (∫ x in (0 : ℝ)..1, ‖polynomial a N x‖^2) = ∑ i ∈ range N, (a i)^2 := by
  have h := polynomial_parseval_complex a N
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq,
    intervalIntegral.integral_ofReal] at h
  exact_mod_cast h

noncomputable def hilbertSum (a b : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ range N, ∑ j ∈ range N, a i * b j / ((j : ℝ) - i)

lemma hilbertSum_integral (a b : ℕ → ℝ) (N : ℕ) :
    ((hilbertSum a b N : ℝ) : ℂ) = (2 * (Real.pi : ℂ) * I) *
      (∫ x in (0 : ℝ)..1, (x - 1/2 : ℝ) *
        (polynomial b N x * conj (polynomial a N x))) := by
  have he (x : ℝ) :
      (x - 1/2 : ℝ) * (polynomial b N x * conj (polynomial a N x)) =
      ∑ i ∈ range N, ∑ j ∈ range N, ((a i * b j : ℝ) : ℂ) *
        ((x - 1/2 : ℝ) * (monomial j x * conj (monomial i x))) := by
    rw [polynomial_product, mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  have hc (i j : ℕ) : Continuous (fun x : ℝ => ((a i * b j : ℝ) : ℂ) *
        ((x - 1/2 : ℝ) * (monomial j x * conj (monomial i x)))) := by fun_prop
  simp_rw [he]
  rw [intervalIntegral.integral_finset_sum (fun i _ =>
    (continuous_finset_sum (range N) fun j _ => hc i j).intervalIntegrable 0 1)]
  simp_rw [intervalIntegral.integral_finset_sum (fun j _ => (hc _ j).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, mul_sum]
  simp only [hilbertSum, ofReal_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [show 2*(Real.pi : ℂ)*I * (((a i*b j : ℝ) : ℂ) *
      (∫ x in (0 : ℝ)..1, (x-1/2 : ℝ)*(monomial j x*conj (monomial i x)))) =
      ((a i*b j : ℝ) : ℂ) * (2*(Real.pi : ℂ)*I *
      (∫ x in (0 : ℝ)..1, (x-1/2 : ℝ)*(monomial j x*conj (monomial i x)))) by ring]
  rw [monomial_bernoulli_integral]
  push_cast
  ring

lemma bernoulli_product_norm_le (z w : ℂ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖(x-1/2 : ℝ) * (w * conj z)‖ ≤ (1/4 : ℝ) * (‖z‖^2+‖w‖^2) := by
  have hb : |x-1/2| ≤ (1/2 : ℝ) := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_conj]
  have h := mul_le_mul_of_nonneg_right hb (mul_nonneg (norm_nonneg w) (norm_nonneg z))
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

/-- A finite Hilbert inequality, with an energy bound sufficient for bounded
observables. Its constant does not depend on the length of the sequences. -/
theorem hilbertSum_energy_bound (a b : ℕ → ℝ) (N : ℕ) :
    |hilbertSum a b N| ≤ Real.pi/2 *
      ((∑ i ∈ range N, (a i)^2)+(∑ i ∈ range N, (b i)^2)) := by
  let J : ℂ := ∫ x in (0 : ℝ)..1, (x-1/2 : ℝ) *
    (polynomial b N x * conj (polynomial a N x))
  have hJ : ‖J‖ ≤ (1/4 : ℝ) *
      ((∑ i ∈ range N, (a i)^2)+(∑ i ∈ range N, (b i)^2)) := by
    calc
      ‖J‖ ≤ ∫ x in (0 : ℝ)..1,
          ‖(x-1/2 : ℝ) * (polynomial b N x * conj (polynomial a N x))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ x in (0 : ℝ)..1, (1/4 : ℝ) *
          (‖polynomial a N x‖^2 + ‖polynomial b N x‖^2) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (Continuous.intervalIntegrable (by fun_prop) 0 1)
          (Continuous.intervalIntegrable (by fun_prop) 0 1)
        intro x hx
        exact bernoulli_product_norm_le _ _ x hx
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 1)
          (Continuous.intervalIntegrable (by fun_prop) 0 1),
          polynomial_parseval, polynomial_parseval]
  have hc : ‖2*(Real.pi : ℂ)*I‖ = 2*Real.pi := by
    norm_num [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    |hilbertSum a b N| = ‖((hilbertSum a b N : ℝ) : ℂ)‖ := by
      rw [norm_real, Real.norm_eq_abs]
    _ = 2*Real.pi*‖J‖ := by rw [hilbertSum_integral, norm_mul, hc]
    _ ≤ 2*Real.pi*((1/4 : ℝ)*
        ((∑ i ∈ range N, (a i)^2)+(∑ i ∈ range N, (b i)^2))) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = _ := by ring

/-- Uniform signed cancellation compared with the O(N log N) absolute
mass of the full harmonic kernel. No arithmetic assumptions are used. -/
theorem hilbertSum_bounded (a b : ℕ → ℝ) (N : ℕ)
    (ha : ∀ i ∈ range N, |a i| ≤ 1) (hb : ∀ i ∈ range N, |b i| ≤ 1) :
    |hilbertSum a b N| ≤ Real.pi*N := by
  have henergy (c : ℕ → ℝ) (hc : ∀ i ∈ range N, |c i| ≤ 1) :
      (∑ i ∈ range N, (c i)^2) ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ range N, (1 : ℝ) := by
        apply sum_le_sum
        intro i hi
        have h := (abs_le.mp (hc i hi))
        nlinarith [sq_nonneg (c i)]
      _ = _ := by simp
  have h := mul_le_mul_of_nonneg_left
    (add_le_add (henergy a ha) (henergy b hb)) (by positivity : 0 ≤ Real.pi/2)
  exact (hilbertSum_energy_bound a b N).trans (by nlinarith)

/-- Each unordered pair contributes exactly once, weighted by the reciprocal
of its positive gap. -/
noncomputable def harmonicSkew (a b : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ range N, ∑ j ∈ range N,
    if i < j then (a i*b j-b i*a j)/((j : ℝ)-i) else 0

lemma harmonicSkew_eq_hilbertSum (a b : ℕ → ℝ) (N : ℕ) :
    harmonicSkew a b N = hilbertSum a b N := by
  have ht (i j : ℕ) : a i*b j/((j : ℝ)-i) =
      (if i < j then a i*b j/((j : ℝ)-i) else 0) -
      (if j < i then a i*b j/((i : ℝ)-j) else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.not_gt]
    · subst j; simp
    · simp only [h, h.not_gt, if_true, if_false, zero_sub]
      rw [show (j : ℝ)-i = -((i : ℝ)-j) by ring, div_neg]
  have hs : (∑ i ∈ range N, ∑ j ∈ range N,
      if j < i then a i*b j/((i : ℝ)-j) else 0) =
      ∑ i ∈ range N, ∑ j ∈ range N,
        if i < j then b i*a j/((j : ℝ)-i) else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    simp only [mul_comm]
  unfold hilbertSum
  conv_rhs =>
    enter [2, i, 2, j]
    rw [ht]
  simp only [sum_sub_distrib]
  rw [hs, ← sum_sub_distrib]
  unfold harmonicSkew
  apply sum_congr rfl
  intro i hi
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  split_ifs <;> ring

/-- The bound retains the signs in the antisymmetric correlation. -/
theorem harmonicSkew_bounded (a b : ℕ → ℝ) (N : ℕ)
    (ha : ∀ i ∈ range N, |a i| ≤ 1) (hb : ∀ i ∈ range N, |b i| ≤ 1) :
    |harmonicSkew a b N| ≤ Real.pi*N := by
  rw [harmonicSkew_eq_hilbertSum]
  exact hilbertSum_bounded a b N ha hb

noncomputable def smoothHarmonicSkew (B C N : ℕ) : ℝ :=
  harmonicSkew (fun n => smoothIndicator B (n+1))
    (fun n => smoothIndicator C (n+1)) N

/-- Both moving smoothness cutoffs are unrestricted. This is a harmonic
average over gaps, not the consecutive-integer skew. -/
theorem smoothHarmonicSkew_bound (B C N : ℕ) :
    |smoothHarmonicSkew B C N| ≤ Real.pi*N := by
  apply harmonicSkew_bounded
  · intro i hi; unfold smoothIndicator; split_ifs <;> norm_num
  · intro i hi; unfold smoothIndicator; split_ifs <;> norm_num

lemma smoothHarmonicSkew_normalized_bound (B C N : ℕ) (hN : 1 < N) :
    |smoothHarmonicSkew B C N/((N : ℝ)*Real.log N)| ≤ Real.pi/Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  rw [abs_div, abs_of_pos (mul_pos hN0 hlog)]
  apply (div_le_iff₀ (mul_pos hN0 hlog)).mpr
  have he : Real.pi/Real.log N*((N : ℝ)*Real.log N) = Real.pi*N := by field_simp
  rw [he]
  exact smoothHarmonicSkew_bound B C N

open Filter in
/-- Uniform cancellation for the actual smooth indicators in this
harmonically gap-averaged statistic. It supplies no transfer to gap one. -/
theorem smoothHarmonicSkew_tendsto (B C : ℕ → ℕ) :
    Tendsto (fun N => smoothHarmonicSkew (B N) (C N) N/((N : ℝ)*Real.log N))
      atTop (nhds 0) := by
  have hl := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := hl.inv_tendsto_atTop.const_mul Real.pi
  simp only [mul_zero] at h
  apply squeeze_zero_norm' _ h
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  simpa only [Real.norm_eq_abs, div_eq_mul_inv, Pi.inv_apply] using
    smoothHarmonicSkew_normalized_bound (B N) (C N) N hN

#print axioms hilbertSum_energy_bound
#print axioms harmonicSkew_bounded
#print axioms smoothHarmonicSkew_tendsto

end HarmonicGap
end Erdos371
