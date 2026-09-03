import Submission.ContinuousBuchstabOperator

/-! A slower exponential supersolution for the continuous two-step kernel.
Its decay rate 2/3 is below log 2, which is useful when a logarithmic cost
profile is evaluated even at the smallest prime. This is an analytic model
estimate; no uniform finite-prime error estimate is asserted here. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 1800000

noncomputable def slowMajorant (u : ℝ) : ℝ :=
  (u^4-20*u^3+149*u^2-550*u+1296)/2592

lemma reciprocal_quartic_majorant (u : ℝ) (hu : 0 ≤ u) :
    1/(u+2) ≤ slowMajorant u := by
  have hh := mul_nonneg hu (mul_nonneg (sq_nonneg (u-2)) (sq_nonneg (u-7)))
  have he : ((u+2)*slowMajorant u-1)*2592=u*(u-2)^2*(u-7)^2 := by
    unfold slowMajorant
    ring
  apply (div_le_iff₀ (by linarith : 0 < u+2)).mpr
  nlinarith only [hh,he]

lemma slowMajorant_nonneg (u : ℝ) (hu : 0 ≤ u) : 0 ≤ slowMajorant u :=
  (by positivity : 0 ≤ 1/(u+2)).trans (reciprocal_quartic_majorant u hu)

noncomputable def slowPrimitive (a t : ℝ) : ℝ :=
  -exp ((-2/3 : ℝ)*t)*
    ((t-a)^4-14*(t-a)^3+86*(t-a)^2-292*(t-a)+858)/1728

lemma slowPrimitive_hasDerivAt (a t : ℝ) :
    HasDerivAt (slowPrimitive a) (exp ((-2/3 : ℝ)*t)*slowMajorant (t-a)) t := by
  have hh := (((((hasDerivAt_id t).const_mul (-2/3 : ℝ)).exp).neg).mul
    (((((((hasDerivAt_id t).sub_const a).pow 4).sub
      ((((hasDerivAt_id t).sub_const a).pow 3).const_mul 14)).add
        ((((hasDerivAt_id t).sub_const a).pow 2).const_mul 86)).sub
          (((hasDerivAt_id t).sub_const a).const_mul 292)).add_const 858)).div_const 1728
  convert hh using 1 <;> dsimp [slowPrimitive,slowMajorant] <;> ring

lemma slowPolynomial_tendsto :
    Tendsto (fun t : ℝ => exp ((-2/3 : ℝ)*t)*(t^4-14*t^3+86*t^2-292*t+858)/1728)
      atTop (𝓝 0) := by
  have hp (n : ℕ) : Tendsto (fun t : ℝ => t^n*exp ((-2/3 : ℝ)*t)) atTop (𝓝 0) := by
    simpa only [rpow_natCast,neg_div] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) (2/3) (by norm_num)
  have hh := (((((hp 4).sub ((hp 3).const_mul 14)).add ((hp 2).const_mul 86)).sub
    ((hp 1).const_mul 292)).add ((hp 0).const_mul 858)).div_const 1728
  convert hh using 1
  · funext t
    ring
  · norm_num

lemma slowPrimitive_tendsto (a : ℝ) : Tendsto (slowPrimitive a) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t-a) atTop atTop := tendsto_atTop_add_const_right _ (-a) tendsto_id
  have hh := ((slowPolynomial_tendsto.comp ht).const_mul (-exp ((-2/3 : ℝ)*a)))
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards with t
  dsimp only [Function.comp_def,slowPrimitive]
  have he : exp ((-2/3 : ℝ)*a)*exp ((-2/3 : ℝ)*(t-a))=exp ((-2/3 : ℝ)*t) := by
    rw [← exp_add]
    congr 1
    ring
  rw [neg_mul,mul_div_assoc,← mul_assoc,he]
  ring

lemma slowMajorant_integrable (a : ℝ) :
    IntegrableOn (fun t : ℝ => exp ((-2/3 : ℝ)*t)*slowMajorant (t-a)) (Ioi a) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => slowPrimitive_hasDerivAt a t)
    (fun t ht => mul_nonneg (exp_pos _).le (slowMajorant_nonneg _ (by linarith [mem_Ioi.mp ht])))
    (slowPrimitive_tendsto a)

lemma integral_slowMajorant (a : ℝ) :
    (∫ t : ℝ in Ioi a, exp ((-2/3 : ℝ)*t)*slowMajorant (t-a)) =
      (143/288 : ℝ)*exp ((-2/3 : ℝ)*a) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => slowPrimitive_hasDerivAt a t) (slowMajorant_integrable a) (slowPrimitive_tendsto a)]
  unfold slowPrimitive
  ring

lemma slow_div_majorant (a t : ℝ) (ha : 2 ≤ a) (ht : a ≤ t) :
    exp ((-2/3 : ℝ)*t)/t ≤ exp ((-2/3 : ℝ)*t)*slowMajorant (t-a) := by
  have hh := (one_div_le_one_div_of_le (by linarith : 0 < t-a+2)
    (show t-a+2 ≤ t by linarith)).trans (reciprocal_quartic_majorant (t-a) (by linarith))
  have hm := mul_le_mul_of_nonneg_left hh (exp_pos ((-2/3 : ℝ)*t)).le
  simpa only [mul_one_div] using hm

lemma integrable_slow_exp_div (a : ℝ) (ha : 2 ≤ a) :
    IntegrableOn (fun t : ℝ => exp ((-2/3 : ℝ)*t)/t) (Ioi a) := by
  apply (slowMajorant_integrable a).mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact (continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.div
      continuousOn_id (fun t ht => by dsimp; linarith [mem_Ioi.mp ht])
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs,abs_of_pos (div_pos (exp_pos _) (by linarith [mem_Ioi.mp ht]))]
    exact slow_div_majorant a t ha (mem_Ioi.mp ht).le

lemma integral_slow_exp_div_le (a : ℝ) (ha : 2 ≤ a) :
    (∫ t : ℝ in Ioi a, exp ((-2/3 : ℝ)*t)/t) ≤ (1/2 : ℝ)*exp ((-2/3 : ℝ)*a) := by
  have hh := setIntegral_mono_on (integrable_slow_exp_div a ha)
    (slowMajorant_integrable a) measurableSet_Ioi
    (fun t ht => slow_div_majorant a t ha (mem_Ioi.mp ht).le)
  rw [integral_slowMajorant] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by norm_num) (exp_pos _).le)

lemma exp_four_thirds_lt : exp (4/3 : ℝ) < 19/5 := by
  have h1 : exp 1 < (87/32 : ℝ) := exp_one_lt_d9.trans (by norm_num)
  have he : (exp (4/3 : ℝ))^3=(exp 1)^4 := by
    rw [← exp_nat_mul,← exp_nat_mul]
    norm_num
  apply (pow_lt_pow_iff_left₀ (exp_pos _).le (by norm_num : (0 : ℝ) ≤ 19/5)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [he]
  exact (pow_lt_pow_left₀ h1 (exp_pos _).le (by norm_num : (4 : ℕ) ≠ 0)).trans (by norm_num)

lemma slow_exp_cutoff_comparison (s : ℝ) (hs : 1 ≤ s) :
    3*exp ((2/3 : ℝ)*(s+1-max 2 (s-1))) ≤ s*exp (4/3 : ℝ) := by
  by_cases h3 : s ≤ 3
  · rw [max_eq_left (by linarith : s-1 ≤ 2)]
    have hh := convexOn_exp.2 (show (0 : ℝ) ∈ univ by trivial)
      (show (4/3 : ℝ) ∈ univ by trivial) (show 0 ≤ (3-s)/2 by linarith)
      (show 0 ≤ (s-1)/2 by linarith) (show (3-s)/2+(s-1)/2=1 by ring)
    simp only [smul_eq_mul,exp_zero,mul_zero,zero_add,mul_one] at hh
    have he : (s-1)/2*(4/3)=(2/3 : ℝ)*(s+1-2) := by ring
    rw [he] at hh
    have hE : (3 : ℝ) ≤ exp (4/3 : ℝ) := by
      linarith [quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4/3)]
    have hm := mul_nonneg (show 0 ≤ 3-s by linarith) (sub_nonneg.mpr hE)
    nlinarith only [hh,hm]
  · rw [max_eq_right (by linarith : 2 ≤ s-1),
      show (2/3 : ℝ)*(s+1-(s-1))=4/3 by ring]
    exact mul_le_mul_of_nonneg_right (by linarith : 3 ≤ s) (exp_pos _).le

lemma kernel_slow_exp_eq (s : ℝ) :
    kernel (fun v => exp ((-2/3 : ℝ)*v)) s =
      ((3/2 : ℝ)*exp (2/3))*
        (∫ t : ℝ in Ioi (max 2 (s-1)), exp ((-2/3 : ℝ)*t)/t)/s := by
  unfold kernel
  simp_rw [integral_exp_mul_Ioi (by norm_num : (-2/3 : ℝ) < 0)]
  have he (t : ℝ) : -exp ((-2/3 : ℝ)*(t-1))/(-2/3)/t=
      ((3/2 : ℝ)*exp (2/3))*(exp ((-2/3 : ℝ)*t)/t) := by
    rw [show (-2/3 : ℝ)*(t-1)=2/3+(-2/3)*t by ring,exp_add]
    ring
  simp_rw [he]
  rw [integral_const_mul]

/-- The slower decay rate still has the same strict contraction factor. -/
theorem kernel_slow_exp_le (s : ℝ) (hs : 1 ≤ s) :
    kernel (fun v => exp ((-2/3 : ℝ)*v)) s ≤ (19/20 : ℝ)*exp ((-2/3 : ℝ)*s) := by
  have hs0 : 0 < s := by linarith
  let a := max 2 (s-1)
  have ha : 2 ≤ a := le_max_left _ _
  have hh := integral_slow_exp_div_le a ha
  rw [kernel_slow_exp_eq]
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (3/2 : ℝ)*exp (2/3))) hs0.le).trans
  have hc := (slow_exp_cutoff_comparison s hs).trans
    (mul_le_mul_of_nonneg_left exp_four_thirds_lt.le hs0.le)
  have hm := mul_le_mul_of_nonneg_right hc (exp_pos ((-2/3 : ℝ)*s)).le
  have he : exp ((2/3 : ℝ)*(s+1-a))*exp ((-2/3 : ℝ)*s)=
      exp (2/3)*exp ((-2/3 : ℝ)*a) := by
    rw [← exp_add,← exp_add]
    congr 1
    ring
  change 3*exp ((2/3 : ℝ)*(s+1-a))*exp ((-2/3 : ℝ)*s) ≤
    s*(19/5)*exp ((-2/3 : ℝ)*s) at hm
  rw [mul_assoc,he] at hm
  apply (div_le_iff₀ hs0).mpr
  nlinarith only [hm]

/-- The continuous positive error operator at inverse-logarithm scale is
conjugate to the original model kernel. -/
noncomputable def logCostKernel (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi (max 2 (s-1)), (∫ v : ℝ in Ioi (t-1), F v/v)/t

lemma logCostKernel_conjugate (u : ℝ → ℝ) (s : ℝ) (hs : 0 < s) :
    logCostKernel (fun v => v*u v) s=s*kernel u s := by
  unfold logCostKernel kernel
  rw [mul_div_cancel₀ _ hs.ne']
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  have ht2 : 2 < t := (le_max_left _ _).trans_lt (mem_Ioi.mp ht)
  have hv0 : v ≠ 0 := by linarith [mem_Ioi.mp hv]
  field_simp

/-- Strict contraction of a logarithmically saved continuous cost profile.
An arithmetic transfer to the actual finite-prime recursion is still needed. -/
theorem logCostKernel_slow_exp_le (s : ℝ) (hs : 1 ≤ s) :
    logCostKernel (fun v => v*exp ((-2/3 : ℝ)*v)) s ≤
      (19/20 : ℝ)*(s*exp ((-2/3 : ℝ)*s)) := by
  rw [logCostKernel_conjugate _ s (by linarith)]
  have hh := mul_le_mul_of_nonneg_left (kernel_slow_exp_le s hs) (by linarith : 0 ≤ s)
  simpa only [mul_left_comm] using hh

#print axioms kernel_slow_exp_le
#print axioms logCostKernel_slow_exp_le
end Erdos970.ContinuousBuchstab
