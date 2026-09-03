import Submission.PrimeSmoothDivisorEstimate
import Submission.ExactLargeDivisorFirstMoment
import Submission.SmoothTailScales
import Submission.DampedMeanMonotonic

/-! A genuine prime-input / smooth-output mean at arbitrarily large
irrational good scales, with the parameter held fixed. No uniform moving-
parameter estimate and no genuine prime-pair lower bound is asserted. -/
namespace Erdos972PrimeSmoothMeanScales

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimeSmoothDivisorEstimate Erdos972PrimeLeastFactorScales
open Erdos972PrimeRoughOutputs Erdos972PrimePowerError Erdos972SmoothDivisorTail
open Erdos972SmoothTailScales Erdos972FixedDampedCorrelation Erdos972DivisorCovariance
open Erdos972ExactLargeDivisorFirstMoment Erdos972PolynomialRowScales
open Erdos972SelbergLowerTest Erdos972ChebyshevPNT Erdos972DampedMeanMonotonic

set_option autoImplicit false
set_option maxHeartbeats 3000000
attribute [local irreducible] root64

lemma slowParameter_tendsto_zero : Tendsto slowParameter atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop sqrt_log_tendsto

lemma fixed_damping_log_tendsto {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Tendsto (fun u : ℕ => damping t (root64 u)*(1+Real.log u)^k) atTop (𝓝 0) := by
  have hh := (slow_damping_weight_tendsto k).mul (slowParameter_tendsto_zero.pow 2)
  simp only [zero_mul] at hh
  have hslow : Tendsto (fun u : ℕ =>
      damping (slowParameter u) (root64 u)*(1+Real.log u)^k) atTop (𝓝 0) := by
    apply hh.congr'
    filter_upwards with u
    exact div_mul_cancel₀ _ (pow_ne_zero 2 (slowParameter_pos u).ne')
  apply squeeze_zero' (Eventually.of_forall (fun u =>
    mul_nonneg (damping_pos t (root64 u)).le (by positivity [Real.log_natCast_nonneg u]))) _ hslow
  filter_upwards [(tendsto_order.mp slowParameter_tendsto_zero).2 t ht] with u hu
  apply mul_le_mul_of_nonneg_right _ (by positivity [Real.log_natCast_nonneg u])
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_natCast_nonneg (root64 u)
  have hm := mul_le_mul_of_nonneg_right hu.le hlog
  linarith only [hm]

lemma direct_scale_tail_bound {α t : ℝ} (hα : 1 ≤ α) {u : ℕ}
    (hu : 0 < u) (hαu : α ≤ u) :
    Real.log (u^6:ℕ)*damping t (root64 u)*(floorMul α (u^6):ℝ)*
        (1+Real.log (floorMul α (u^6))) ≤
      (42*α*damping t (root64 u)*(1+Real.log u)^2)*(u:ℝ)^6 := by
  have hNpos : 0 < u^6 := Nat.pow_pos hu
  have hgpos := floorMul_pos hα hNpos
  have hg : (floorMul α (u^6):ℝ) ≤ α*(u:ℝ)^6 := by
    exact (floorMul_le_real hα (le_refl (u^6))).trans_eq (by norm_cast)
  have hgpow : (floorMul α (u^6):ℝ) ≤ (u:ℝ)^7 := by
    have hh := mul_le_mul_of_nonneg_right hαu (pow_nonneg (Nat.cast_nonneg u) 6)
    nlinarith only [hg, hh]
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hgpos) hgpow
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hdamp := (damping_pos t (root64 u)).le
  have hapos : 0 ≤ α := le_trans (by norm_num) hα
  have hlogu := Real.log_natCast_nonneg u
  have hL : 1+Real.log (floorMul α (u^6)) ≤ 7*(1+Real.log u) := by linarith only [hlog]
  have hNlog : Real.log (u^6:ℕ) ≤ 6*(1+Real.log u) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  calc
    _ ≤ (6*(1+Real.log u))*damping t (root64 u)*(α*(u:ℝ)^6)*(7*(1+Real.log u)) := by
      gcongr
    _ = _ := by ring

lemma prime_smooth_normalized_error {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t) {u : ℕ}
    (hu : 0 < u) (hαu : α ≤ u)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ root64 u →
      |row (Ioc 0 (u^6)) primeWeight (floorMul α) d-Chebyshev.psi (u^6:ℕ)/(d:ℝ)| ≤ primeRowError u) :
    |mixedPrimeSmooth t α (u^6)/(u:ℝ)^6-
        (Chebyshev.psi (u^6:ℕ)/(u:ℝ)^6)*(divisorMean (root64 u) (dampedCoefficient t)/t)| ≤
      ((root64 u:ℝ)*primeRowError u/(u:ℝ)^6+
        42*α*damping t (root64 u)*(1+Real.log u)^2)/t := by
  have hfin := prime_smooth_finite_estimate hα ht (primeRowError_nonneg u) (root64 u) (u^6) hrows
  have htail := direct_scale_tail_bound (t := t) hα hu hαu
  have hbound := hfin.trans (add_le_add_right htail (primeRowError u*(root64 u:ℝ)))
  have hNR : (0:ℝ) < (u:ℝ)^6 := pow_pos (Nat.cast_pos.mpr hu) _
  have hden : 0 < t*(u:ℝ)^6 := mul_pos ht hNR
  have he : mixedPrimeSmooth t α (u^6)/(u:ℝ)^6-
      (Chebyshev.psi (u^6:ℕ)/(u:ℝ)^6)*(divisorMean (root64 u) (dampedCoefficient t)/t) =
      (t*mixedPrimeSmooth t α (u^6)-Chebyshev.psi (u^6:ℕ)*divisorMean (root64 u) (dampedCoefficient t))/(t*(u:ℝ)^6) := by
    field_simp
  rw [he, abs_div, abs_of_pos hden]
  apply (div_le_div_of_nonneg_right hbound hden.le).trans_eq
  field_simp

noncomputable def primeSmoothMain (t : ℝ) (u : ℕ) : ℝ :=
  (Chebyshev.psi (u^6:ℕ)/(u:ℝ)^6)*(divisorMean (root64 u) (dampedCoefficient t)/t)

lemma primeSmoothMain_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (primeSmoothMain t) atTop (𝓝 (dampedMean t/t)) := by
  have hpow : Tendsto (fun u : ℕ => u^6) atTop atTop := tendsto_pow_atTop (by decide)
  have hψ := psi_div_self_tendsto.comp (tendsto_natCast_atTop_atTop.comp hpow)
  have hD := ((divisorMean_tendsto ht).comp root64_tendsto).div_const t
  unfold primeSmoothMain
  simpa only [Function.comp_apply, Nat.cast_pow, one_mul] using hψ.mul hD

noncomputable def primeSmoothErrorBudget (t α : ℝ) (u : ℕ) : ℝ :=
  ((root64 u:ℝ)*primeRowError u/(u:ℝ)^6+
    42*α*damping t (root64 u)*(1+Real.log u)^2)/t+
      |primeSmoothMain t u-dampedMean t/t|

lemma primeSmoothErrorBudget_tendsto {t : ℝ} (ht : 0 < t) (α : ℝ) :
    Tendsto (primeSmoothErrorBudget t α) atTop (𝓝 0) := by
  have hd := (fixed_damping_log_tendsto ht 2).const_mul (42*α)
  have hm := ((primeSmoothMain_tendsto ht).sub_const (dampedMean t/t)).abs
  simp only [mul_zero, sub_self, abs_zero] at hd hm
  have hh := ((primeRowError_weighted_tendsto.add hd).div_const t).add hm
  unfold primeSmoothErrorBudget
  simpa only [mul_assoc, zero_add, zero_div, add_zero] using hh

lemma prime_smooth_error_budget {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t) {u : ℕ}
    (hu : 0 < u) (hαu : α ≤ u)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ root64 u →
      |row (Ioc 0 (u^6)) primeWeight (floorMul α) d-Chebyshev.psi (u^6:ℕ)/(d:ℝ)| ≤ primeRowError u) :
    |mixedPrimeSmooth t α (u^6)/(u:ℝ)^6-dampedMean t/t| ≤ primeSmoothErrorBudget t α u := by
  have hh := abs_sub_le (mixedPrimeSmooth t α (u^6)/(u:ℝ)^6)
    (primeSmoothMain t u) (dampedMean t/t)
  exact hh.trans (add_le_add_left (prime_smooth_normalized_error hα ht hu hαu hrows) _)

/-- At arbitrarily large actual irrational scales the normalized mixed sum
is as close as desired to its positive fixed-parameter mean. -/
theorem exists_prime_smooth_mean_scale {α t ε : ℝ} (hα : 1 < α) (hI : Irrational α)
    (ht : 0 < t) (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 0 < u ∧
      |mixedPrimeSmooth t α (u^6)/(u:ℝ)^6-dampedMean t/t| < ε := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_order.mp (primeSmoothErrorBudget_tendsto ht α)).2 ε hε).and
      (eventually_ge_atTop ⌈α⌉₊))
  obtain ⟨u, hBu, hu, hbudget, hrows⟩ :=
    exists_small_prime_prefix_rows hα hI (by norm_num : (0:ℝ) < 1) (max B T)
  have hTu : T ≤ u := (le_max_right B T).trans hBu.le
  obtain ⟨he, hαu⟩ := hT u hTu
  have hαu' : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr hαu)
  refine ⟨u, (le_max_left B T).trans_lt hBu, hu, ?_⟩
  exact (prime_smooth_error_budget hα.le ht hu hαu'
    (fun d hd hdv => hrows d hd hdv (u^6) le_rfl)).trans_lt he

/-- An unconditional positive lower bound with a genuine prime INPUT
weight. The smoothed output factor is NOT a primality assertion. -/
theorem exists_prime_smooth_positive_scale {α t : ℝ} (hα : 1 < α) (hI : Irrational α)
    (ht : 0 < t) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ (dampedMean t/(2*t))*(u:ℝ)^6 < mixedPrimeSmooth t α (u^6) := by
  have hA : 0 < dampedMean t/t := div_pos (dampedMean_pos ht) ht
  obtain ⟨u, hBu, hu, he⟩ := exists_prime_smooth_mean_scale hα hI ht
    (show 0 < (dampedMean t/t)/2 by positivity) B
  have hlo := (abs_lt.mp he).1
  have hNR : (0:ℝ) < (u:ℝ)^6 := pow_pos (Nat.cast_pos.mpr hu) _
  have hh : dampedMean t/(2*t) < mixedPrimeSmooth t α (u^6)/(u:ℝ)^6 := by
    have hid : dampedMean t/(2*t) = (dampedMean t/t)/2 := by ring
    rw [hid]
    linarith only [hlo]
  exact ⟨u, hBu, (lt_div_iff₀ hNR).mp hh⟩

#print axioms prime_smooth_normalized_error
#print axioms primeSmoothErrorBudget_tendsto
#print axioms exists_prime_smooth_mean_scale
#print axioms exists_prime_smooth_positive_scale

end Erdos972PrimeSmoothMeanScales
