import FormalConjecturesUtil

/-! An exponential supersolution for a continuous two-step Buchstab kernel.
This file concerns the analytic model only, not the finite-prime sieve. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 1000000

lemma reciprocal_quadratic_majorant (u : ℝ) (hu : 0 ≤ u) :
    1/(u+2) ≤ (u^2-6*u+16)/32 := by
  apply (div_le_iff₀ (by linarith : 0 < u+2)).mpr
  have hh := mul_nonneg hu (sq_nonneg (u-2))
  nlinarith only [hh]

lemma shifted_reciprocal_majorant (a t : ℝ) (ha : 2 ≤ a) (ht : a ≤ t) :
    exp (-t)/t ≤ exp (-t)*((t-a)^2-6*(t-a)+16)/32 := by
  have h1 : 1/t ≤ 1/((t-a)+2) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hh := mul_le_mul_of_nonneg_left
    (h1.trans (reciprocal_quadratic_majorant (t-a) (by linarith))) (exp_pos (-t)).le
  convert hh using 1 <;> ring

lemma shifted_majorant_hasDerivAt (a t : ℝ) :
    HasDerivAt (fun x : ℝ => -exp (-x)*((x-a)^2-4*(x-a)+12)/32)
      (exp (-t)*((t-a)^2-6*(t-a)+16)/32) t := by
  have hh := ((((hasDerivAt_id t).neg.exp).neg).mul
    (((((hasDerivAt_id t).sub_const a).pow 2).sub
      (((hasDerivAt_id t).sub_const a).const_mul 4)).add_const 12)).div_const 32
  convert hh using 1 <;> dsimp <;> ring

lemma shifted_majorant_tendsto (a : ℝ) :
    Tendsto (fun x : ℝ => -exp (-x)*((x-a)^2-4*(x-a)+12)/32)
      atTop (𝓝 0) := by
  have h2 := tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have h1 := tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h0 := tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have hh := ((h2.sub (h1.const_mul (2*a+4))).add
    (h0.const_mul (a^2+4*a+12))).neg.div_const 32
  convert hh using 1
  · funext x
    ring
  · norm_num

lemma shifted_majorant_nonneg (a t : ℝ) :
    0 ≤ exp (-t)*((t-a)^2-6*(t-a)+16)/32 := by
  have hp : 0 ≤ (t-a)^2-6*(t-a)+16 := by nlinarith [sq_nonneg (t-a-3)]
  positivity

lemma integrable_shifted_majorant (a : ℝ) :
    IntegrableOn (fun t : ℝ => exp (-t)*((t-a)^2-6*(t-a)+16)/32) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => shifted_majorant_hasDerivAt a t)
    (fun t _ => shifted_majorant_nonneg a t) (shifted_majorant_tendsto a)

lemma integral_shifted_majorant (a : ℝ) :
    (∫ t : ℝ in Ioi a, exp (-t)*((t-a)^2-6*(t-a)+16)/32) =
      (3/8 : ℝ)*exp (-a) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => shifted_majorant_hasDerivAt a t)
    (integrable_shifted_majorant a) (shifted_majorant_tendsto a)]
  ring

lemma integrable_exp_div (a : ℝ) (ha : 2 ≤ a) :
    IntegrableOn (fun t : ℝ => exp (-t)/t) (Ioi a) := by
  apply (integrable_shifted_majorant a).mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact (Real.continuous_exp.comp continuous_neg).continuousOn.div
      continuousOn_id (fun t ht => by dsimp; linarith [mem_Ioi.mp ht])
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (exp_pos _) (by linarith [mem_Ioi.mp ht]))]
    exact shifted_reciprocal_majorant a t ha (mem_Ioi.mp ht).le

/-- A rational moment bound for the exponential integral, uniform over the
starting point. The nonnegative error is u*(u-2)^2/(32*(u+2)). -/
theorem integral_exp_div_le (a : ℝ) (ha : 2 ≤ a) :
    (∫ t : ℝ in Ioi a, exp (-t)/t) ≤ (3/8 : ℝ)*exp (-a) := by
  rw [← integral_shifted_majorant a]
  exact setIntegral_mono_on (integrable_exp_div a ha)
    (integrable_shifted_majorant a) measurableSet_Ioi
    (fun t ht => shifted_reciprocal_majorant a t ha (mem_Ioi.mp ht).le)

/-- The two-step upper-excess operator with the square cutoff retained. -/
noncomputable def kernel (u : ℝ → ℝ) (s : ℝ) : ℝ :=
  (∫ t : ℝ in Ioi (max 2 (s-1)), (∫ v : ℝ in Ioi (t-1), u v)/t)/s

lemma kernel_exp_eq (s : ℝ) :
    kernel (fun v => exp (-v)) s =
      exp 1*(∫ t : ℝ in Ioi (max 2 (s-1)), exp (-t)/t)/s := by
  unfold kernel
  simp_rw [integral_exp_neg_Ioi, show ∀ t : ℝ, -(t-1)=1+(-t) by intro t; ring,
    exp_add, mul_div_assoc]
  rw [integral_const_mul]
  ring

lemma exp_cutoff_comparison (s : ℝ) (hs : 1 ≤ s) :
    3*exp (s+1-max 2 (s-1)) ≤ s*exp 2 := by
  by_cases h3 : s ≤ 3
  · rw [max_eq_left (by linarith : s-1 ≤ 2)]
    have hh := convexOn_exp.2 (show (0 : ℝ) ∈ univ by trivial)
      (show (2 : ℝ) ∈ univ by trivial) (show 0 ≤ (3-s)/2 by linarith)
      (show 0 ≤ (s-1)/2 by linarith) (show (3-s)/2+(s-1)/2=1 by ring)
    simp only [smul_eq_mul, exp_zero, mul_zero, zero_add, mul_one] at hh
    have he : (s-1)/2*2 = s-1 := by ring
    rw [he] at hh
    have hE : 3 ≤ exp 2 := by linarith [add_one_le_exp (2 : ℝ)]
    have hp := mul_nonneg (show 0 ≤ 3-s by linarith) (show 0 ≤ exp 2-3 by linarith)
    have he' : s+1-2=s-1 := by ring
    rw [he']
    nlinarith only [hh,hp]
  · rw [max_eq_right (by linarith : 2 ≤ s-1)]
    rw [show s+1-(s-1)=2 by ring]
    exact mul_le_mul_of_nonneg_right (by linarith : 3 ≤ s) (exp_pos _).le

lemma exp_two_lt_thirty_eight_fifths : exp 2 < (38/5 : ℝ) := by
  have h1 : exp 1 < (11/4 : ℝ) := exp_one_lt_d9.trans (by norm_num)
  have he : exp 2 = (exp 1)^2 := by rw [← exp_nat_mul]; norm_num
  rw [he]
  nlinarith [exp_pos (1 : ℝ)]

/-- The continuous upper-excess kernel contracts the exponential envelope.
The constant is explicit and independent of the refinement depth. -/
theorem kernel_exp_le (s : ℝ) (hs : 1 ≤ s) :
    kernel (fun v => exp (-v)) s ≤ (19/20 : ℝ)*exp (-s) := by
  have hs0 : 0 < s := by linarith
  let a := max 2 (s-1)
  have ha : 2 ≤ a := le_max_left _ _
  have hh := integral_exp_div_le a ha
  rw [kernel_exp_eq]
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hh (exp_pos 1).le) hs0.le).trans
  have hc := exp_cutoff_comparison s hs
  have hE : exp 2 ≤ (38/5 : ℝ) := exp_two_lt_thirty_eight_fifths.le
  have ht : 3*exp (s+1-a) ≤ s*(38/5 : ℝ) :=
    hc.trans (mul_le_mul_of_nonneg_left hE hs0.le)
  have hh' := mul_le_mul_of_nonneg_right ht (exp_pos (-s)).le
  have he : exp (s+1-a)*exp (-s) = exp 1*exp (-a) := by
    rw [← exp_add, ← exp_add]
    congr 1
    dsimp [a]
    ring
  rw [mul_assoc,he] at hh'
  apply (div_le_iff₀ hs0).mpr
  nlinarith only [hh']

#print axioms integral_exp_div_le
#print axioms kernel_exp_le
end Erdos970.ContinuousBuchstab
