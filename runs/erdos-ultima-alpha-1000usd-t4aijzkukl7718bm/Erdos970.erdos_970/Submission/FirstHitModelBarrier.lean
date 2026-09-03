import Submission.FirstHitIntegerCutoff

/-! An analytic obstruction for the specified continuous first-hit normalizer
model at exponent two. This is NOT an obstruction to every sieve, and is NOT
a disproof of the quadratic Jacobsthal conjecture. No asymptotic identification
of an arithmetic normalizer is assumed without an explicit hypothesis. -/
namespace Erdos970.FirstHitModelBarrier
open Finset Real Set MeasureTheory
open FiniteSelberg

lemma gamma_lower : (143/250 : ℝ) < eulerMascheroniConstant := by
  have hhR : (5425/1000 : ℝ) ≤ (harmonic 127 : ℝ) := by
    norm_num [harmonic, sum_range_succ]
  have hg := eulerMascheroniSeq_lt_eulerMascheroniConstant 127
  have he : eulerMascheroniSeq 127 = (harmonic 127 : ℝ)-7*log 2 := by
    rw [eulerMascheroniSeq]
    norm_num only [Nat.cast_ofNat]
    rw [show (128 : ℝ) = 2^7 by norm_num, log_pow]
    norm_num
  rw [he] at hg
  linarith [log_two_lt_d9]

lemma exp_gamma_lower : (177/100 : ℝ) < exp eulerMascheroniConstant := by
  have hh := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 143/250) 5
  norm_num [sum_range_succ] at hh
  have he := exp_lt_exp.mpr gamma_lower
  linarith

/-- A quadratic upper envelope for the exact initial normalizer profile. -/
lemma initial_profile_le_parabola (u : ℝ) (hu : u ∈ Icc (1 : ℝ) 2) :
    firstHitProfile u ≤ u-(u-1)^2/4 := by
  let f : ℝ → ℝ := fun x => x*log x-x+1-(x-1)^2/4
  let g : ℝ → ℝ := fun x => log x-(x-1)/2
  have hd (x : ℝ) (hx : x ∈ Icc (1 : ℝ) 2) : HasDerivAt f (g x) x := by
    have hx0 : x ≠ 0 := by linarith [hx.1]
    convert (((((hasDerivAt_id x).mul (hasDerivAt_log hx0)).sub (hasDerivAt_id x)).add_const 1).sub
      ((((hasDerivAt_id x).sub_const 1).pow 2).div_const 4)) using 1
    dsimp [f,g]
    field_simp
    ring
  have hg (x : ℝ) (hx : x ∈ Icc (1 : ℝ) 2) : 0 ≤ g x := by
    have hx0 : 0 < x := by linarith [hx.1]
    have hl := one_sub_inv_le_log_of_pos hx0
    have ht : (x-1)/2 ≤ 1-x⁻¹ := by
      apply (mul_le_mul_iff_right₀ hx0).mp
      have he : x*(1-x⁻¹) = x-1 := by field_simp
      rw [he]
      nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)]
    dsimp [g]
    linarith
  have hf : MonotoneOn f (Icc (1 : ℝ) 2) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 2)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => hg x (interior_subset hx))
  have hh := hf (by norm_num : (1 : ℝ) ∈ Icc (1 : ℝ) 2) hu hu.1
  norm_num [f] at hh
  unfold firstHitProfile
  linarith

noncomputable def reciprocalLower (u : ℝ) : ℝ := 1/u+(u-1)^2/(4*u^2)

lemma reciprocal_lower_le (u : ℝ) (hu : u ∈ Icc (1 : ℝ) 2) :
    reciprocalLower u ≤ firstHitReciprocal u := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hpos := firstHitProfile_pos u (show u ∈ Icc (1 : ℝ) 3 by constructor <;> linarith [hu.1,hu.2])
  have hup := initial_profile_le_parabola u hu
  have hsum : 0 ≤ u+(u-1)^2/4 := by positivity
  have hm := mul_le_mul_of_nonneg_right hup hsum
  have he : reciprocalLower u = (u+(u-1)^2/4)/u^2 := by
    unfold reciprocalLower
    field_simp
  rw [he, firstHitReciprocal]
  apply (div_le_div_iff₀ (sq_pos_of_pos hu0) hpos).mpr
  nlinarith only [hm, sq_nonneg ((u-1)^2/4)]

lemma reciprocalLower_integral :
    (∫ u in (1 : ℝ)..2, reciprocalLower u) = log 2/2+3/8 := by
  let F : ℝ → ℝ := fun u => log u/2+u/4-u⁻¹/4
  have hc : ContinuousOn reciprocalLower (Icc (1 : ℝ) 2) := by
    unfold reciprocalLower
    apply ContinuousOn.add
    · exact continuousOn_const.div continuousOn_id (fun u hu => by linarith [hu.1])
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      positivity
  have hd (u : ℝ) (hu : u ∈ uIcc (1 : ℝ) 2) : HasDerivAt F (reciprocalLower u) u := by
    have hu' : u ∈ Icc (1 : ℝ) 2 := by simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hu
    have hu0 : u ≠ 0 := by linarith [hu'.1]
    convert (((hasDerivAt_log hu0).div_const 2).add ((hasDerivAt_id u).div_const 4)).sub
      ((hasDerivAt_inv hu0).div_const 4) using 1
    dsimp [F,reciprocalLower]
    field_simp
    ring
  have hi : IntervalIntegrable reciprocalLower volume (1 : ℝ) 2 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hc
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  norm_num [F] at hh
  linarith only [hh]

lemma initial_reciprocal_integral_lower :
    log 2/2+3/8 ≤ ∫ u in (1 : ℝ)..2, firstHitReciprocal u := by
  rw [← reciprocalLower_integral]
  have hc : ContinuousOn reciprocalLower (uIcc (1 : ℝ) 2) := by
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    unfold reciprocalLower
    apply ContinuousOn.add
    · exact continuousOn_const.div continuousOn_id (fun u hu => by linarith [hu.1])
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      positivity
  have hi : IntervalIntegrable firstHitReciprocal volume (1 : ℝ) 2 := by
    apply ContinuousOn.intervalIntegrable
    apply firstHitReciprocal_continuous.mono
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    intro u hu
    exact ⟨hu.1, hu.2.trans (by norm_num)⟩
  exact intervalIntegral.integral_mono_on (by norm_num) hc.intervalIntegrable hi reciprocal_lower_le

/-- The two explicit initial profile pieces alone exceed the entire critical
normalized budget. In particular no nonnegative tail can correct the sign. -/
theorem truncated_critical_excess (E : ℝ) (hE : 177/100 ≤ E) :
    1/125 < 2*(E*(log 2+(∫ u in (1 : ℝ)..2, firstHitReciprocal u))-3/2)-2 := by
  have hJ := initial_reciprocal_integral_lower
  have hl := log_two_gt_d9
  have hJ0 : 0 ≤ log 2+(∫ u in (1 : ℝ)..2, firstHitReciprocal u) := by linarith
  have hh := mul_le_mul_of_nonneg_right hE hJ0
  nlinarith only [hJ,hl,hh]

/-- The comparison applies to every positive continuous model with these
explicit upper envelopes on its initial pieces. No claim is made here that
all arithmetic kernels or all sieve schemes have such a model. -/
lemma model_initial_integral_lower (G : ℝ → ℝ)
    (hG : ContinuousOn G (Icc (1/2 : ℝ) 2))
    (hpos : ∀ u ∈ Icc (1/2 : ℝ) 2, 0 < G u)
    (hsmall : ∀ u ∈ Icc (1/2 : ℝ) 1, G u ≤ u)
    (hmid : ∀ u ∈ Icc (1 : ℝ) 2, G u ≤ firstHitProfile u) :
    log 2+(∫ u in (1 : ℝ)..2, firstHitReciprocal u) ≤
      ∫ u in (1/2 : ℝ)..2, 1/G u := by
  have hc : ContinuousOn (fun u => 1/G u) (Icc (1/2 : ℝ) 2) :=
    continuousOn_const.div hG (fun u hu => (hpos u hu).ne')
  have hi (a b : ℝ) (ha : 1/2 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
      IntervalIntegrable (fun u => 1/G u) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply hc.mono
    rw [uIcc_of_le hab]
    intro u hu
    exact ⟨ha.trans hu.1,hu.2.trans hb⟩
  have hi0 : IntervalIntegrable (fun u : ℝ => 1/u) volume (1/2 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)]
    exact continuousOn_const.div continuousOn_id (fun u hu => by linarith [hu.1])
  have hfirst := intervalIntegral.integral_mono_on (by norm_num : (1/2 : ℝ) ≤ 1)
    hi0 (hi (1/2) 1 (by norm_num) (by norm_num) (by norm_num))
    (fun u hu => one_div_le_one_div_of_le
      (hpos u ⟨hu.1,hu.2.trans (by norm_num)⟩) (hsmall u hu))
  have he : (∫ u in (1/2 : ℝ)..1, 1/u) = log 2 := by
    rw [integral_one_div_of_pos (by norm_num) (by norm_num)]
    norm_num
  rw [he] at hfirst
  have himid : IntervalIntegrable firstHitReciprocal volume (1 : ℝ) 2 := by
    apply ContinuousOn.intervalIntegrable
    apply firstHitReciprocal_continuous.mono
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    intro u hu
    exact ⟨hu.1,hu.2.trans (by norm_num)⟩
  have hsecond := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 2)
    himid (hi 1 2 (by norm_num) (by norm_num) (by norm_num))
    (fun u hu => one_div_le_one_div_of_le
      (hpos u ⟨(by norm_num : (1/2 : ℝ) ≤ 1).trans hu.1,hu.2⟩) (hmid u hu))
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hi (1/2) 1 (by norm_num) (by norm_num) (by norm_num))
    (hi 1 2 (by norm_num) (by norm_num) (by norm_num))
  linarith only [hfirst,hsecond,hadd]

/-- At exponent two, the normalized margin in the stated first-hit model
is strictly negative, even before adding any nonnegative remaining tail. -/
theorem critical_model_margin_negative (G : ℝ → ℝ)
    (hG : ContinuousOn G (Icc (1/2 : ℝ) 2))
    (hpos : ∀ u ∈ Icc (1/2 : ℝ) 2, 0 < G u)
    (hsmall : ∀ u ∈ Icc (1/2 : ℝ) 1, G u ≤ u)
    (hmid : ∀ u ∈ Icc (1 : ℝ) 2, G u ≤ firstHitProfile u)
    (E T : ℝ) (hE : 177/100 ≤ E) (hT : 0 ≤ T) :
    2-2*((∫ u in (1/2 : ℝ)..2, (E/G u-1))+T) < -1/125 := by
  have hJ := model_initial_integral_lower G hG hpos hsmall hmid
  have hcritical := truncated_critical_excess E hE
  have hmul := mul_le_mul_of_nonneg_left hJ (show 0 ≤ E by linarith)
  have hi : IntervalIntegrable (fun u => 1/G u) volume (1/2 : ℝ) 2 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)]
    exact continuousOn_const.div hG (fun u hu => (hpos u hu).ne')
  have he : (∫ u in (1/2 : ℝ)..2, (E/G u-1)) =
      E*(∫ u in (1/2 : ℝ)..2, 1/G u)-3/2 := by
    have hf : (fun u => E/G u-1) = (fun u => E*(1/G u)-1) := by
      funext u
      ring
    rw [hf,intervalIntegral.integral_sub (hi.const_mul E) (continuous_const.intervalIntegrable (1/2) 2),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
    norm_num [smul_eq_mul]
  rw [he]
  linarith only [hcritical,hmul,hT]

/-- The same analytic obstruction uses the actual Euler--Mascheroni constant;
the elementary numerical bound on its exponential is kernel checked above. -/
theorem critical_gamma_model_margin_negative (G : ℝ → ℝ)
    (hG : ContinuousOn G (Icc (1/2 : ℝ) 2))
    (hpos : ∀ u ∈ Icc (1/2 : ℝ) 2, 0 < G u)
    (hsmall : ∀ u ∈ Icc (1/2 : ℝ) 1, G u ≤ u)
    (hmid : ∀ u ∈ Icc (1 : ℝ) 2, G u ≤ firstHitProfile u)
    (T : ℝ) (hT : 0 ≤ T) :
    2-2*((∫ u in (1/2 : ℝ)..2, (exp eulerMascheroniConstant/G u-1))+T) < -1/125 :=
  critical_model_margin_negative G hG hpos hsmall hmid
    (exp eulerMascheroniConstant) T exp_gamma_lower.le hT

#print axioms exp_gamma_lower
#print axioms initial_profile_le_parabola
#print axioms truncated_critical_excess
#print axioms critical_gamma_model_margin_negative
end Erdos970.FirstHitModelBarrier
