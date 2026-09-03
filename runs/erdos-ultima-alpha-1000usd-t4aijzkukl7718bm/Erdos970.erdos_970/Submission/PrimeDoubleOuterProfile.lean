import Submission.PrimeSmoothProfileTransfer
import Submission.ContinuousBuchstabSlowKernel

/-! The coefficient-one arithmetic transfer for the leading outer profile of
the square-guarded two-step error operator. The final recursion is not yet
established in this file. -/
namespace Erdos970.WeightedMertens
open Finset Real Set MeasureTheory Erdos970.ContinuousBuchstab
set_option maxHeartbeats 1800000

noncomputable def doubleOuterProfile (L u : ℝ) : ℝ :=
  exp ((-2/3 : ℝ)*(L-u)/u)/((2/3 : ℝ)*u*(L-u))
noncomputable def doubleOuterDeriv (L u : ℝ) : ℝ :=
  exp ((-2/3 : ℝ)*(L-u)/u)*((L-u)*((2/3 : ℝ)*L-u)+u^2)/
    ((2/3 : ℝ)*u^3*(L-u)^2)

lemma doubleOuter_hasDerivAt (L u : ℝ) (hu : u ≠ 0) (hLu : L-u ≠ 0) :
    HasDerivAt (doubleOuterProfile L) (doubleOuterDeriv L u) u := by
  have he := (((((hasDerivAt_id u).const_sub L).const_mul (-2/3 : ℝ)).div
    (hasDerivAt_id u) hu).exp)
  have hd := ((hasDerivAt_id u).const_mul (2/3 : ℝ)).mul ((hasDerivAt_id u).const_sub L)
  have hh := he.div hd (mul_ne_zero (mul_ne_zero (by norm_num) hu) hLu)
  convert hh using 1
  dsimp [doubleOuterDeriv]
  field_simp
  ring

lemma doubleOuterDeriv_nonneg (L u : ℝ) (hu : 0 < u) (hLu : 3*u ≤ L) :
    0 ≤ doubleOuterDeriv L u := by
  have h1 : 0 ≤ L-u := by linarith
  have h2 : 0 ≤ (2/3 : ℝ)*L-u := by linarith
  unfold doubleOuterDeriv
  positivity

lemma doubleOuterProfile_nonneg (L u : ℝ) (hu : 0 ≤ u) (hLu : u ≤ L) :
    0 ≤ doubleOuterProfile L u := by
  unfold doubleOuterProfile
  have hh : 0 ≤ L-u := sub_nonneg.mpr hLu
  positivity

lemma doubleOuterDeriv_continuous (L c U : ℝ) (hc : 0 < c) (hUL : U < L) :
    ContinuousOn (doubleOuterDeriv L) (Icc c U) := by
  intro u hu
  have hu0 : u ≠ 0 := (hc.trans_le hu.1).ne'
  have hLu : L-u ≠ 0 := by linarith [hu.2]
  have hden : (2/3 : ℝ)*u^3*(L-u)^2 ≠ 0 := by positivity
  apply ContinuousAt.continuousWithinAt
  unfold doubleOuterDeriv
  fun_prop (disch := assumption)

lemma doubleOuterProfile_integrable (L c U : ℝ) (hc : 0 < c) (hcU : c ≤ U) (hUL : U < L) :
    IntervalIntegrable (doubleOuterProfile L) volume c U := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hcU]
  apply ContinuousOn.integrableOn_Icc
  intro u hu
  have hu0 : u ≠ 0 := (hc.trans_le hu.1).ne'
  have hLu : L-u ≠ 0 := by linarith [hu.2]
  exact (doubleOuter_hasDerivAt L u hu0 hLu).continuousAt.continuousWithinAt

/-- Outer arithmetic summation: the leading integral is unchanged and the
endpoint error is only twice the bounded Mertens discrepancy. -/
theorem prime_doubleOuterProfile_upper (R : ℕ) (hR : 2 ≤ R) (L : ℝ)
    (hRL : 3*log (R : ℝ) ≤ L) :
    (∑ p ∈ (R+1).primesBelow,
      exp ((-2/3 : ℝ)*(L-log (p : ℝ))/log (p : ℝ))/((2/3 : ℝ)*(p : ℝ)*(L-log (p : ℝ)))) ≤
      (∫ u in (1/2)..log (R : ℝ), doubleOuterProfile L u)+
        2*smoothProfileError*doubleOuterProfile L (log (R : ℝ)) := by
  have hl : (1/2 : ℝ) ≤ log (R : ℝ) :=
    (by linarith [log_two_gt_d9] : (1/2 : ℝ) ≤ log 2).trans
      (log_le_log (by norm_num) (by exact_mod_cast hR))
  have hUL : log (R : ℝ) < L := by linarith
  have hg : IntervalIntegrable (doubleOuterDeriv L) volume (1/2) (log (R : ℝ)) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hl]
    exact (doubleOuterDeriv_continuous L _ _ (by norm_num) hUL).integrableOn_Icc
  have hh := prime_monotone_profile_upper R hR (doubleOuterProfile L) (doubleOuterDeriv L) hg
    (by
      intro u hu
      exact doubleOuter_hasDerivAt L u (by linarith [hu.1]) (by linarith [hu.2]))
    (by
      intro u hu
      exact doubleOuterProfile_nonneg L u (by linarith [hu.1]) (by linarith [hu.2]))
    (by
      intro u hu
      exact doubleOuterDeriv_nonneg L u (by linarith [hu.1]) (by linarith [hu.2]))
  have he : (∑ p ∈ (R+1).primesBelow, (log (p : ℝ)/(p : ℝ))*doubleOuterProfile L (log (p : ℝ))) =
      ∑ p ∈ (R+1).primesBelow,
        exp ((-2/3 : ℝ)*(L-log (p : ℝ))/log (p : ℝ))/((2/3 : ℝ)*(p : ℝ)*(L-log (p : ℝ))) := by
    apply sum_congr rfl
    intro p hp
    have hlp : log (p : ℝ) ≠ 0 := (log_pos (by exact_mod_cast (mem_primes.mp hp).1.one_lt)).ne'
    unfold doubleOuterProfile
    field_simp
  rwa [he] at hh


/-- Change of variables retains the exact exponentially decaying tail of the
continuous model. No separate crude bound is taken for the two prime sums. -/
lemma integral_doubleOuterProfile_le_tail (L c U : ℝ) (hc : 0 < c) (hcU : c ≤ U)
    (hUL : 3*U ≤ L) :
    (∫ u in c..U,doubleOuterProfile L u) ≤
      (3/(2*L))*(∫ t : ℝ in Ioi (L/U-1), exp ((-2/3 : ℝ)*t)/t) := by
  have hU : 0 < U := hc.trans_le hcU
  have hL : 0 < L := by linarith
  have hU' : U < L := by linarith
  let φ : ℝ → ℝ := fun u => L/u-1
  let φ' : ℝ → ℝ := fun u => -L/u^2
  let ψ : ℝ → ℝ := fun t => exp ((-2/3 : ℝ)*t)/t
  have hφ (u : ℝ) (hu : u ∈ uIcc c U) : HasDerivAt φ (φ' u) u := by
    rw [uIcc_of_le hcU] at hu
    have hu0 : u ≠ 0 := (hc.trans_le hu.1).ne'
    have hh := ((hasDerivAt_const u L).div (hasDerivAt_id u) hu0).sub_const 1
    convert hh using 1
    dsimp only [φ']
    simp
  have hφ' : ContinuousOn φ' (uIcc c U) := by
    rw [uIcc_of_le hcU]
    intro u hu
    have hu0 : u ≠ 0 := (hc.trans_le hu.1).ne'
    apply ContinuousAt.continuousWithinAt
    dsimp only [φ']
    fun_prop (disch := exact pow_ne_zero _ hu0)
  have hψ : ContinuousOn ψ (φ '' uIcc c U) := by
    intro t ht
    obtain ⟨u,hu,rfl⟩ := ht
    rw [uIcc_of_le hcU] at hu
    have hu0 : 0 < u := hc.trans_le hu.1
    have hcut : (2 : ℝ) ≤ φ u := by
      dsimp [φ]
      have hh : 3 ≤ L/u := (le_div_iff₀ hu0).mpr (by linarith [hu.2])
      linarith
    have ht0 : φ u ≠ 0 := by linarith
    apply ContinuousAt.continuousWithinAt
    dsimp only [ψ]
    fun_prop (disch := assumption)
  have hsub := intervalIntegral.integral_comp_mul_deriv' hφ hφ' hψ
  have he : (∫ u in c..U,(ψ ∘ φ) u*φ' u) =
      (-2/3 : ℝ)*L*(∫ u in c..U,doubleOuterProfile L u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hcU] at hu
    have hu0 : u ≠ 0 := (hc.trans_le hu.1).ne'
    have hLu : L-u ≠ 0 := by linarith [hu.2]
    dsimp only [Function.comp_def,φ,φ',ψ,doubleOuterProfile]
    have harg : (-2/3 : ℝ)*(L/u-1)=(-2/3 : ℝ)*(L-u)/u := by field_simp <;> ring
    rw [harg]
    field_simp <;> ring
  rw [he,intervalIntegral.integral_symm (φ U) (φ c)] at hsub
  have ha : (2 : ℝ) ≤ φ U := by
    dsimp [φ]
    have hh : 3 ≤ L/U := (le_div_iff₀ hU).mpr hUL
    linarith
  have hab : φ U ≤ φ c := by
    dsimp only [φ]
    exact sub_le_sub_right (div_le_div_of_nonneg_left hL.le hc hcU) 1
  have hmono : (∫ t in φ U..φ c,ψ t) ≤ ∫ t : ℝ in Ioi (φ U), ψ t := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_mono_set (integrable_slow_exp_div (φ U) ha)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact div_nonneg (exp_pos _).le (by linarith [mem_Ioi.mp ht])
    · exact Ioc_subset_Ioi_self.eventuallyLE
  have hh : (2*L)*(∫ u in c..U,doubleOuterProfile L u) ≤
      3*(∫ t : ℝ in Ioi (φ U),ψ t) := by
    linarith only [hsub,hmono]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 2*L)).mpr
  convert hh using 1 <;> dsimp only [φ,ψ] <;> ring

/-- The previously verified exponential-integral majorant gives this explicit
outer main bound. -/
lemma integral_doubleOuterProfile_upper (L c U : ℝ) (hc : 0 < c) (hcU : c ≤ U)
    (hUL : 3*U ≤ L) :
    (∫ u in c..U,doubleOuterProfile L u) ≤
      (3/(4*L))*exp ((-2/3 : ℝ)*(L/U-1)) := by
  have hU : 0 < U := hc.trans_le hcU
  have hL : 0 < L := by linarith
  have ha : (2 : ℝ) ≤ L/U-1 := by
    have hh : 3 ≤ L/U := (le_div_iff₀ hU).mpr hUL
    linarith
  have hh := mul_le_mul_of_nonneg_left (integral_slow_exp_div_le (L/U-1) ha)
    (by positivity : (0 : ℝ) ≤ 3/(2*L))
  apply (integral_doubleOuterProfile_le_tail L c U hc hcU hUL).trans
  convert hh using 1 <;> ring


#print axioms integral_doubleOuterProfile_upper
#print axioms prime_doubleOuterProfile_upper
end Erdos970.WeightedMertens
