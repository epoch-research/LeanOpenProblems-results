import Submission.PrimeSmoothProfileTransfer

/-! Coefficient-one prime summation for a decaying exponential reciprocal-log
profile. This is a quantitative arithmetic input for the two-step cost
operator; it is not a complete recursion or a Jacobsthal endpoint result. -/
namespace Erdos970.WeightedMertens
open Finset Real Set MeasureTheory
set_option maxHeartbeats 2000000

noncomputable def reciprocalExpSquare (a t : ℝ) : ℝ := exp (-a/t)/t^2
noncomputable def reciprocalExpSquareDeriv (a t : ℝ) : ℝ := exp (-a/t)*(a-2*t)/t^4
noncomputable def reciprocalExpVariationPrimitive (a t : ℝ) : ℝ :=
  exp (-a/t)*(1/t^2+4/(a*t)+4/a^2)
noncomputable def reciprocalExpVariationMajorant (a t : ℝ) : ℝ := exp (-a/t)*(a+2*t)/t^4

lemma reciprocalExpSquare_hasDerivAt (a t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (reciprocalExpSquare a) (reciprocalExpSquareDeriv a t) t := by
  have hh := ((((hasDerivAt_const t (-a)).div (hasDerivAt_id t) ht).exp).div
    ((hasDerivAt_id t).pow 2) (pow_ne_zero _ ht))
  convert hh using 1
  dsimp [reciprocalExpSquareDeriv]
  field_simp <;> ring

lemma reciprocalExpSquare_primitive (a t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ => exp (-a/x)/a) (reciprocalExpSquare a t) t := by
  have hh := (((hasDerivAt_const t (-a)).div (hasDerivAt_id t) ht).exp).div_const a
  convert hh using 1
  dsimp [reciprocalExpSquare]
  field_simp <;> ring

lemma reciprocalExpVariationPrimitive_hasDerivAt (a t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (reciprocalExpVariationPrimitive a) (reciprocalExpVariationMajorant a t) t := by
  have he := ((hasDerivAt_const t (-a)).div (hasDerivAt_id t) ht).exp
  have h1 := (hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).pow 2) (pow_ne_zero _ ht)
  have h2 := (hasDerivAt_const t (4 : ℝ)).div ((hasDerivAt_id t).const_mul a) (mul_ne_zero ha ht)
  have hh := he.mul ((h1.add h2).add_const (4/a^2))
  convert hh using 1
  dsimp [reciprocalExpVariationMajorant]
  field_simp <;> ring

lemma reciprocalExpSquare_continuous (a c U : ℝ) (hc : 0 < c) :
    ContinuousOn (reciprocalExpSquare a) (Icc c U) := by
  intro t ht
  exact (reciprocalExpSquare_hasDerivAt a t (by linarith [ht.1])).continuousAt.continuousWithinAt

lemma reciprocalExpSquareDeriv_continuous (a c U : ℝ) (hc : 0 < c) :
    ContinuousOn (reciprocalExpSquareDeriv a) (Icc c U) := by
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  apply ContinuousAt.continuousWithinAt
  unfold reciprocalExpSquareDeriv
  fun_prop (disch := first | exact ht0 | exact pow_ne_zero _ ht0)

lemma reciprocalExpVariationMajorant_continuous (a c U : ℝ) (hc : 0 < c) :
    ContinuousOn (reciprocalExpVariationMajorant a) (Icc c U) := by
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  apply ContinuousAt.continuousWithinAt
  unfold reciprocalExpVariationMajorant
  fun_prop (disch := first | exact ht0 | exact pow_ne_zero _ ht0)

lemma reciprocalExpSquareDeriv_abs_le (a t : ℝ) (ha : 0 ≤ a) (ht : 0 < t) :
    |reciprocalExpSquareDeriv a t| ≤ reciprocalExpVariationMajorant a t := by
  have hh : |a-2*t| ≤ a+2*t := by
    rw [abs_le]
    constructor <;> linarith
  unfold reciprocalExpSquareDeriv reciprocalExpVariationMajorant
  rw [abs_div,abs_mul,abs_of_pos (exp_pos _),abs_of_pos (pow_pos ht 4)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (exp_pos _).le) (pow_nonneg ht.le 4)

lemma reciprocalExpVariationPrimitive_nonneg (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    0 ≤ reciprocalExpVariationPrimitive a t := by
  unfold reciprocalExpVariationPrimitive
  positivity

lemma reciprocalExpVariationPrimitive_upper (a U : ℝ) (hU : 0 < U)
    (ha : (4/3 : ℝ)*U ≤ a) :
    reciprocalExpVariationPrimitive a U ≤ (25/4 : ℝ)*reciprocalExpSquare a U := by
  have ha0 : 0 < a := (mul_pos (by norm_num) hU).trans_le ha
  have hr0 : 0 ≤ U/a := div_nonneg hU.le ha0.le
  have hr : U/a ≤ (3/4 : ℝ) := (div_le_iff₀ ha0).mpr (by linarith only [ha])
  have hr2 := pow_le_pow_left₀ hr0 hr 2
  have hc : 1+4*(U/a)+4*(U/a)^2 ≤ (25/4 : ℝ) := by norm_num at hr2; linarith only [hr,hr2]
  have hf : 0 ≤ reciprocalExpSquare a U := by unfold reciprocalExpSquare; positivity
  have he : reciprocalExpVariationPrimitive a U =
      reciprocalExpSquare a U*(1+4*(U/a)+4*(U/a)^2) := by
    unfold reciprocalExpVariationPrimitive reciprocalExpSquare
    field_simp <;> ring
  rw [he]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hc hf

lemma reciprocalExpSquare_variation_bound (a c U : ℝ) (hc : 0 < c) (hcU : c ≤ U)
    (ha : (4/3 : ℝ)*U ≤ a) :
    |reciprocalExpSquare a U|+(∫ t in c..U, |reciprocalExpSquareDeriv a t|) ≤
      8*reciprocalExpSquare a U := by
  have hU : 0 < U := hc.trans_le hcU
  have ha0 : 0 < a := (mul_pos (by norm_num) hU).trans_le ha
  have hg : IntervalIntegrable (reciprocalExpSquareDeriv a) volume c U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hcU]
    exact (reciprocalExpSquareDeriv_continuous a c U hc).integrableOn_Icc
  have hJ : IntervalIntegrable (reciprocalExpVariationMajorant a) volume c U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hcU]
    exact (reciprocalExpVariationMajorant_continuous a c U hc).integrableOn_Icc
  have hi := intervalIntegral.integral_mono_on hcU hg.abs hJ (by
    intro t ht
    exact reciprocalExpSquareDeriv_abs_le a t ha0.le (hc.trans_le ht.1))
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := reciprocalExpVariationPrimitive a) (f' := reciprocalExpVariationMajorant a)
    (a := c) (b := U) (by
      intro t ht
      rw [uIcc_of_le hcU] at ht
      exact reciprocalExpVariationPrimitive_hasDerivAt a t ha0.ne' (hc.trans_le ht.1).ne') hJ
  rw [hft] at hi
  have hlo := reciprocalExpVariationPrimitive_nonneg a c ha0.le hc.le
  have hup := reciprocalExpVariationPrimitive_upper a U hU ha
  have hf : 0 ≤ reciprocalExpSquare a U := by unfold reciprocalExpSquare; positivity
  rw [abs_of_nonneg hf]
  linarith only [hi,hlo,hup,hf]

lemma integral_reciprocalExpSquare_upper (a c U : ℝ) (ha : 0 < a)
    (hc : 0 < c) (hcU : c ≤ U) :
    (∫ t in c..U, reciprocalExpSquare a t) ≤ exp (-a/U)/a := by
  have hi : IntervalIntegrable (reciprocalExpSquare a) volume c U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hcU]
    exact (reciprocalExpSquare_continuous a c U hc).integrableOn_Icc
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => exp (-a/x)/a)
    (f' := reciprocalExpSquare a) (by
      intro t ht
      rw [uIcc_of_le hcU] at ht
      exact reciprocalExpSquare_primitive a t ha.ne' (hc.trans_le ht.1).ne') hi]
  exact sub_le_self _ (div_nonneg (exp_pos _).le ha.le)

/-- A sharp leading exponential integral and a uniformly lower-order arithmetic
remainder. The parameter condition is exactly the one furnished by the cube
guard in a two-step square-guarded recursion at decay rate 2/3. -/
theorem prime_reciprocalExpSquare_sum_upper (R : ℕ) (hR : 2 ≤ R) (a : ℝ)
    (ha : (4/3 : ℝ)*log (R : ℝ) ≤ a) :
    (∑ p ∈ (R+1).primesBelow, exp (-a/log (p : ℝ))/((p : ℝ)*log (p : ℝ))) ≤
      exp (-a/log (R : ℝ))*(1/a+8*smoothProfileError/log (R : ℝ)^2) := by
  have hl : (1/2 : ℝ) ≤ log (R : ℝ) :=
    (by linarith [log_two_gt_d9] : (1/2 : ℝ) ≤ log 2).trans
      (log_le_log (by norm_num) (by exact_mod_cast hR))
  have hl0 : 0 < log (R : ℝ) := by linarith
  have ha0 : 0 < a := (mul_pos (by norm_num) hl0).trans_le ha
  have hg : IntervalIntegrable (reciprocalExpSquareDeriv a) volume (1/2) (log (R : ℝ)) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hl]
    exact (reciprocalExpSquareDeriv_continuous a _ _ (by norm_num)).integrableOn_Icc
  have herr := (abs_le.mp (prime_smooth_profile_error R hR
    (reciprocalExpSquare a) (reciprocalExpSquareDeriv a) hg (by
      intro t ht
      exact reciprocalExpSquare_hasDerivAt a t (by linarith [ht.1])))).2
  have hv := mul_le_mul_of_nonneg_left
    (reciprocalExpSquare_variation_bound a (1/2) (log (R : ℝ)) (by norm_num) hl ha)
    smoothProfileError_pos.le
  have hi := integral_reciprocalExpSquare_upper a (1/2) (log (R : ℝ)) ha0 (by norm_num) hl
  have he : (∑ p ∈ (R+1).primesBelow, (log (p : ℝ)/(p : ℝ))*reciprocalExpSquare a (log (p : ℝ))) =
      (∑ p ∈ (R+1).primesBelow, exp (-a/log (p : ℝ))/((p : ℝ)*log (p : ℝ))) := by
    apply sum_congr rfl
    intro p hp
    have hlp : log (p : ℝ) ≠ 0 := (log_pos (by exact_mod_cast (mem_primes.mp hp).1.one_lt)).ne'
    unfold reciprocalExpSquare
    field_simp
  rw [he] at herr
  have hh : (∑ p ∈ (R+1).primesBelow, exp (-a/log (p : ℝ))/((p : ℝ)*log (p : ℝ))) ≤
      exp (-a/log (R : ℝ))/a+smoothProfileError*(8*reciprocalExpSquare a (log (R : ℝ))) := by
    linarith only [herr,hv,hi]
  convert hh using 1
  unfold reciprocalExpSquare
  ring

#print axioms prime_reciprocalExpSquare_sum_upper
#print axioms reciprocalExpSquare_variation_bound
end Erdos970.WeightedMertens
