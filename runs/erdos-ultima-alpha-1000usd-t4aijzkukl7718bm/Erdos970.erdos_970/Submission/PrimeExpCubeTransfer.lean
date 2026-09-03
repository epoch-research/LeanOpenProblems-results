import Submission.PrimeDecayingExponentialTransfer

/-! Coefficient-one prime summation for a decaying exponential reciprocal-log
profile. This is a quantitative arithmetic input for the two-step cost
operator; it is not a complete recursion or a Jacobsthal endpoint result. -/
namespace Erdos970.WeightedMertens
open Finset Real Set MeasureTheory
set_option maxHeartbeats 2000000

noncomputable def reciprocalExpCube (a t : ℝ) : ℝ := exp (-a/t)/t^3
noncomputable def reciprocalExpCubeDeriv (a t : ℝ) : ℝ := exp (-a/t)*(a-3*t)/t^5
noncomputable def reciprocalExpCubeVariationPrimitive (a t : ℝ) : ℝ :=
  exp (-a/t)*(1/t^3+6/(a*t^2)+12/(a^2*t)+12/a^3)
noncomputable def reciprocalExpCubeVariationMajorant (a t : ℝ) : ℝ := exp (-a/t)*(a+3*t)/t^5

lemma reciprocalExpCube_hasDerivAt (a t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (reciprocalExpCube a) (reciprocalExpCubeDeriv a t) t := by
  have hh := ((((hasDerivAt_const t (-a)).div (hasDerivAt_id t) ht).exp).div
    ((hasDerivAt_id t).pow 3) (pow_ne_zero _ ht))
  convert hh using 1
  dsimp [reciprocalExpCubeDeriv]
  field_simp <;> ring

lemma reciprocalExpCube_primitive (a t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ => exp (-a/x)*(a/x+1)/a^2) (reciprocalExpCube a t) t := by
  have he := ((hasDerivAt_const t (-a)).div (hasDerivAt_id t) ht).exp
  have hh := (he.mul (((hasDerivAt_const t a).div (hasDerivAt_id t) ht).add_const 1)).div_const (a^2)
  convert hh using 1
  dsimp [reciprocalExpCube]
  field_simp <;> ring

lemma reciprocalExpCubeVariationPrimitive_hasDerivAt (a t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (reciprocalExpCubeVariationPrimitive a) (reciprocalExpCubeVariationMajorant a t) t := by
  have he := ((hasDerivAt_const t (-a)).div (hasDerivAt_id t) ht).exp
  have h1 := (hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).pow 3) (pow_ne_zero _ ht)
  have h2 := (hasDerivAt_const t (6 : ℝ)).div (((hasDerivAt_id t).pow 2).const_mul a)
    (mul_ne_zero ha (pow_ne_zero _ ht))
  have h3 := (hasDerivAt_const t (12 : ℝ)).div ((hasDerivAt_id t).const_mul (a^2))
    (mul_ne_zero (pow_ne_zero _ ha) ht)
  have hh := he.mul (((h1.add h2).add h3).add_const (12/a^3))
  convert hh using 1
  dsimp [reciprocalExpCubeVariationMajorant]
  field_simp <;> ring

lemma reciprocalExpCube_continuous (a c U : ℝ) (hc : 0 < c) :
    ContinuousOn (reciprocalExpCube a) (Icc c U) := by
  intro t ht
  exact (reciprocalExpCube_hasDerivAt a t (by linarith [ht.1])).continuousAt.continuousWithinAt

lemma reciprocalExpCubeDeriv_continuous (a c U : ℝ) (hc : 0 < c) :
    ContinuousOn (reciprocalExpCubeDeriv a) (Icc c U) := by
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  apply ContinuousAt.continuousWithinAt
  unfold reciprocalExpCubeDeriv
  fun_prop (disch := first | exact ht0 | exact pow_ne_zero _ ht0)

lemma reciprocalExpCubeVariationMajorant_continuous (a c U : ℝ) (hc : 0 < c) :
    ContinuousOn (reciprocalExpCubeVariationMajorant a) (Icc c U) := by
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  apply ContinuousAt.continuousWithinAt
  unfold reciprocalExpCubeVariationMajorant
  fun_prop (disch := first | exact ht0 | exact pow_ne_zero _ ht0)

lemma reciprocalExpCubeDeriv_abs_le (a t : ℝ) (ha : 0 ≤ a) (ht : 0 < t) :
    |reciprocalExpCubeDeriv a t| ≤ reciprocalExpCubeVariationMajorant a t := by
  have hh : |a-3*t| ≤ a+3*t := by
    rw [abs_le]
    constructor <;> linarith
  unfold reciprocalExpCubeDeriv reciprocalExpCubeVariationMajorant
  rw [abs_div,abs_mul,abs_of_pos (exp_pos _),abs_of_pos (pow_pos ht 5)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (exp_pos _).le) (pow_nonneg ht.le 5)

lemma reciprocalExpCubeVariationPrimitive_nonneg (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    0 ≤ reciprocalExpCubeVariationPrimitive a t := by
  unfold reciprocalExpCubeVariationPrimitive
  positivity

lemma reciprocalExpCubeVariationPrimitive_upper (a U : ℝ) (hU : 0 < U)
    (ha : (2 : ℝ)*U ≤ a) :
    reciprocalExpCubeVariationPrimitive a U ≤ (17/2 : ℝ)*reciprocalExpCube a U := by
  have ha0 : 0 < a := (mul_pos (by norm_num) hU).trans_le ha
  have hr0 : 0 ≤ U/a := div_nonneg hU.le ha0.le
  have hr : U/a ≤ (1/2 : ℝ) := (div_le_iff₀ ha0).mpr (by linarith only [ha])
  have hr2 := pow_le_pow_left₀ hr0 hr 2
  have hr3 := pow_le_pow_left₀ hr0 hr 3
  have hc : 1+6*(U/a)+12*(U/a)^2+12*(U/a)^3 ≤ (17/2 : ℝ) := by
    norm_num at hr2 hr3
    linarith only [hr,hr2,hr3]
  have hf : 0 ≤ reciprocalExpCube a U := by unfold reciprocalExpCube; positivity
  have he : reciprocalExpCubeVariationPrimitive a U =
      reciprocalExpCube a U*(1+6*(U/a)+12*(U/a)^2+12*(U/a)^3) := by
    unfold reciprocalExpCubeVariationPrimitive reciprocalExpCube
    field_simp <;> ring
  rw [he]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hc hf

lemma reciprocalExpCube_variation_bound (a c U : ℝ) (hc : 0 < c) (hcU : c ≤ U)
    (ha : (2 : ℝ)*U ≤ a) :
    |reciprocalExpCube a U|+(∫ t in c..U, |reciprocalExpCubeDeriv a t|) ≤
      10*reciprocalExpCube a U := by
  have hU : 0 < U := hc.trans_le hcU
  have ha0 : 0 < a := (mul_pos (by norm_num) hU).trans_le ha
  have hg : IntervalIntegrable (reciprocalExpCubeDeriv a) volume c U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hcU]
    exact (reciprocalExpCubeDeriv_continuous a c U hc).integrableOn_Icc
  have hJ : IntervalIntegrable (reciprocalExpCubeVariationMajorant a) volume c U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hcU]
    exact (reciprocalExpCubeVariationMajorant_continuous a c U hc).integrableOn_Icc
  have hi := intervalIntegral.integral_mono_on hcU hg.abs hJ (by
    intro t ht
    exact reciprocalExpCubeDeriv_abs_le a t ha0.le (hc.trans_le ht.1))
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := reciprocalExpCubeVariationPrimitive a) (f' := reciprocalExpCubeVariationMajorant a)
    (a := c) (b := U) (by
      intro t ht
      rw [uIcc_of_le hcU] at ht
      exact reciprocalExpCubeVariationPrimitive_hasDerivAt a t ha0.ne' (hc.trans_le ht.1).ne') hJ
  rw [hft] at hi
  have hlo := reciprocalExpCubeVariationPrimitive_nonneg a c ha0.le hc.le
  have hup := reciprocalExpCubeVariationPrimitive_upper a U hU ha
  have hf : 0 ≤ reciprocalExpCube a U := by unfold reciprocalExpCube; positivity
  rw [abs_of_nonneg hf]
  linarith only [hi,hlo,hup,hf]

lemma integral_reciprocalExpCube_upper (a c U : ℝ) (ha : 0 < a)
    (hc : 0 < c) (hcU : c ≤ U) :
    (∫ t in c..U, reciprocalExpCube a t) ≤ exp (-a/U)*(a/U+1)/a^2 := by
  have hi : IntervalIntegrable (reciprocalExpCube a) volume c U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hcU]
    exact (reciprocalExpCube_continuous a c U hc).integrableOn_Icc
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => exp (-a/x)*(a/x+1)/a^2)
    (f' := reciprocalExpCube a) (by
      intro t ht
      rw [uIcc_of_le hcU] at ht
      exact reciprocalExpCube_primitive a t ha.ne' (hc.trans_le ht.1).ne') hi]
  exact sub_le_self _ (by positivity)

/-- A sharp leading exponential integral and a uniformly lower-order arithmetic
remainder. The parameter condition is furnished by the outer cube guard in a
two-step square-guarded recursion at decay rate 2/3. -/
theorem prime_reciprocalExpCube_sum_upper (R : ℕ) (hR : 2 ≤ R) (a : ℝ)
    (ha : (2 : ℝ)*log (R : ℝ) ≤ a) :
    (∑ p ∈ (R+1).primesBelow, exp (-a/log (p : ℝ))/((p : ℝ)*log (p : ℝ)^2)) ≤
      exp (-a/log (R : ℝ))*((a/log (R : ℝ)+1)/a^2+10*smoothProfileError/log (R : ℝ)^3) := by
  have hl : (1/2 : ℝ) ≤ log (R : ℝ) :=
    (by linarith [log_two_gt_d9] : (1/2 : ℝ) ≤ log 2).trans
      (log_le_log (by norm_num) (by exact_mod_cast hR))
  have hl0 : 0 < log (R : ℝ) := by linarith
  have ha0 : 0 < a := (mul_pos (by norm_num) hl0).trans_le ha
  have hg : IntervalIntegrable (reciprocalExpCubeDeriv a) volume (1/2) (log (R : ℝ)) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hl]
    exact (reciprocalExpCubeDeriv_continuous a _ _ (by norm_num)).integrableOn_Icc
  have herr := (abs_le.mp (prime_smooth_profile_error R hR
    (reciprocalExpCube a) (reciprocalExpCubeDeriv a) hg (by
      intro t ht
      exact reciprocalExpCube_hasDerivAt a t (by linarith [ht.1])))).2
  have hv := mul_le_mul_of_nonneg_left
    (reciprocalExpCube_variation_bound a (1/2) (log (R : ℝ)) (by norm_num) hl ha)
    smoothProfileError_pos.le
  have hi := integral_reciprocalExpCube_upper a (1/2) (log (R : ℝ)) ha0 (by norm_num) hl
  have he : (∑ p ∈ (R+1).primesBelow, (log (p : ℝ)/(p : ℝ))*reciprocalExpCube a (log (p : ℝ))) =
      (∑ p ∈ (R+1).primesBelow, exp (-a/log (p : ℝ))/((p : ℝ)*log (p : ℝ)^2)) := by
    apply sum_congr rfl
    intro p hp
    have hlp : log (p : ℝ) ≠ 0 := (log_pos (by exact_mod_cast (mem_primes.mp hp).1.one_lt)).ne'
    unfold reciprocalExpCube
    field_simp
  rw [he] at herr
  have hh : (∑ p ∈ (R+1).primesBelow, exp (-a/log (p : ℝ))/((p : ℝ)*log (p : ℝ)^2)) ≤
      exp (-a/log (R : ℝ))*(a/log (R : ℝ)+1)/a^2+smoothProfileError*(10*reciprocalExpCube a (log (R : ℝ))) := by
    linarith only [herr,hv,hi]
  convert hh using 1
  unfold reciprocalExpCube
  ring

#print axioms prime_reciprocalExpCube_sum_upper
#print axioms reciprocalExpCube_variation_bound
end Erdos970.WeightedMertens
