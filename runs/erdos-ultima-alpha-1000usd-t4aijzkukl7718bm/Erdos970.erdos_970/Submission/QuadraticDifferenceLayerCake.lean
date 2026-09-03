import Submission.QuadraticLayerCake

/-! A variation-controlled estimate for differences of the truncated quadratic
profile. The error retains a factor v^2 even as the shift v tends to zero. -/
namespace Erdos970.FiniteSelberg
open Finset Real MeasureTheory

noncomputable def splitSlope (c : ℝ) (g h : ℝ → ℝ) (t : ℝ) : ℝ :=
  g t + if c < t then h t - g t else 0

lemma splitSlope_eq_if (c : ℝ) (g h : ℝ → ℝ) (t : ℝ) :
    splitSlope c g h t = if c < t then h t else g t := by
  unfold splitSlope
  split_ifs <;> ring

lemma splitSlope_integrable (c a b : ℝ) (g h : ℝ → ℝ)
    (hg : Continuous g) (hh : Continuous h) :
    IntervalIntegrable (splitSlope c g h) volume a b := by
  exact (hg.intervalIntegrable a b).add
    (intervalIntegrable_cut ((hh.sub hg).intervalIntegrable a b) c)

lemma integral_cut_between (g : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b) (hcb : c ≤ b) :
    (∫ t in a..b, if c < t then g t else 0) = ∫ t in max a c..b, g t := by
  rw [intervalIntegral.integral_of_le hab]
  change (∫ t in Set.Ioc a b, (Set.Ioi c).indicator g t) = _
  rw [MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.inter_comm, Set.Ioc_inter_Ioi,
    intervalIntegral.integral_of_le (max_le hab hcb)]

lemma integral_splitSlope (c a b : ℝ) (hab : a ≤ b) (hcb : c ≤ b)
    (g h : ℝ → ℝ) (hg : Continuous g) (hh : Continuous h) :
    (∫ t in a..b, splitSlope c g h t) =
      (∫ t in a..b, g t) + (∫ t in max a c..b, h t) - (∫ t in max a c..b, g t) := by
  unfold splitSlope
  rw [intervalIntegral.integral_add (hg.intervalIntegrable a b)
      (intervalIntegrable_cut ((hh.sub hg).intervalIntegrable a b) c),
    integral_cut_between _ a b c hab hcb,
    intervalIntegral.integral_sub (hh.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

def earlySlope (v t : ℝ) : ℝ := -8 * v ^ 2 * t - 4 * v ^ 3

@[fun_prop] lemma earlySlope_continuous (v : ℝ) : Continuous (earlySlope v) := by
  unfold earlySlope
  fun_prop

lemma earlySlope_nonpos (v t : ℝ) (hv : 0 ≤ v) (ht : 0 ≤ t) :
    earlySlope v t ≤ 0 := by
  have he : earlySlope v t = -(4 * v ^ 2 * (2 * t + v)) := by unfold earlySlope; ring
  rw [he]
  exact neg_nonpos.mpr (by positivity)

lemma integral_earlySlope (v a b : ℝ) :
    (∫ t in a..b, earlySlope v t) =
      -4 * v ^ 2 * (b ^ 2 - a ^ 2) - 4 * v ^ 3 * (b - a) := by
  unfold earlySlope
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

lemma integral_earlySlope_mul (v a b : ℝ) :
    (∫ t in a..b, earlySlope v t * t) =
      -(8 / 3) * v ^ 2 * (b ^ 3 - a ^ 3) - 2 * v ^ 3 * (b ^ 2 - a ^ 2) := by
  have he : (fun t => earlySlope v t * t) =
      fun t => (-8 * v ^ 2) * t ^ 2 - (4 * v ^ 3) * t := by
    funext t
    unfold earlySlope
    ring
  rw [he, intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow, integral_id]
    norm_num
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

noncomputable def quadraticDifferenceSlope (L v : ℝ) : ℝ → ℝ :=
  splitSlope (L - v) (earlySlope v) (quadraticSlope L)

lemma quadraticDifferenceSlope_integrable (L v a b : ℝ) :
    IntervalIntegrable (quadraticDifferenceSlope L v) volume a b :=
  splitSlope_integrable _ _ _ _ _ (earlySlope_continuous v) (quadraticSlope_continuous L)

lemma quadratic_difference_primitive (L v x : ℝ) (hv : 0 ≤ v) (hvL : v ≤ L) (hx : 0 ≤ x) :
    (quadraticProfile L x - quadraticProfile L (x + v)) ^ 2 =
      if x ≤ L then (∫ t in x..L, quadraticDifferenceSlope L v t) else 0 := by
  have hL : 0 ≤ L := hv.trans hvL
  by_cases hxL : x ≤ L
  · rw [if_pos hxL]
    unfold quadraticDifferenceSlope
    rw [integral_splitSlope _ _ _ hxL (by linarith) _ _
      (earlySlope_continuous v) (quadraticSlope_continuous L)]
    by_cases hxc : x ≤ L - v
    · rw [max_eq_right hxc, integral_earlySlope, integral_quadraticSlope, integral_earlySlope,
        quadraticProfile, quadraticProfile,
        max_eq_left (by nlinarith : 0 ≤ L ^ 2 - x ^ 2),
        max_eq_left (by nlinarith : 0 ≤ L ^ 2 - (x + v) ^ 2)]
      ring
    · rw [max_eq_left (le_of_not_ge hxc), integral_earlySlope, integral_quadraticSlope,
        quadraticProfile, quadraticProfile,
        max_eq_left (by nlinarith : 0 ≤ L ^ 2 - x ^ 2),
        max_eq_right (by nlinarith : L ^ 2 - (x + v) ^ 2 ≤ 0)]
      ring
  · rw [if_neg hxL, quadraticProfile, quadraticProfile,
      max_eq_right (by nlinarith : L ^ 2 - x ^ 2 ≤ 0),
      max_eq_right (by nlinarith : L ^ 2 - (x + v) ^ 2 ≤ 0)]
    norm_num

lemma integral_quadraticDifferenceSlope_mul (L v : ℝ) (hv : 0 ≤ v) (hvL : v ≤ L) :
    (∫ t in 0..L, quadraticDifferenceSlope L v t * t) =
      (4 / 3) * L ^ 3 * v ^ 2 - (2 / 3) * L ^ 2 * v ^ 3 - (2 / 15) * v ^ 5 := by
  have he : (fun t => quadraticDifferenceSlope L v t * t) =
      splitSlope (L - v) (fun t => earlySlope v t * t) (fun t => quadraticSlope L t * t) := by
    funext t
    simp only [quadraticDifferenceSlope, splitSlope_eq_if]
    split_ifs <;> rfl
  rw [he, integral_splitSlope _ _ _ (hv.trans hvL) (by linarith) _ _
    (by fun_prop) (by fun_prop), max_eq_right (by linarith : 0 ≤ L - v),
    integral_earlySlope_mul, integral_quadraticSlope_mul, integral_earlySlope_mul]
  ring

lemma integral_abs_quadraticDifferenceSlope (L v : ℝ) (hv : 0 ≤ v) (hvL : v ≤ L) :
    (∫ t in 0..L, |quadraticDifferenceSlope L v t|) =
      2 * (2 * L * v - v ^ 2) ^ 2 - v ^ 4 := by
  have hL := hv.trans hvL
  have he : (∫ t in 0..L, |quadraticDifferenceSlope L v t|) =
      ∫ t in 0..L, splitSlope (L - v) (fun t => -earlySlope v t) (quadraticSlope L) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hL] at ht
    simp only [quadraticDifferenceSlope, splitSlope_eq_if]
    split_ifs
    · exact abs_of_nonneg (quadraticSlope_nonneg L t ht.1 ht.2)
    · exact abs_of_nonpos (earlySlope_nonpos v t hv ht.1)
  rw [he, integral_splitSlope _ _ _ hL (by linarith) _ _ (by fun_prop)
    (quadraticSlope_continuous L), max_eq_right (by linarith : 0 ≤ L - v),
    intervalIntegral.integral_neg, intervalIntegral.integral_neg,
    integral_earlySlope, integral_quadraticSlope, integral_earlySlope]
  ring

lemma quadraticDifference_variation_le (L v : ℝ) (hv : 0 ≤ v) (hvL : v ≤ L) :
    (∫ t in 0..L, |quadraticDifferenceSlope L v t|) ≤ 8 * L ^ 2 * v ^ 2 := by
  rw [integral_abs_quadraticDifferenceSlope L v hv hvL]
  have hh := mul_le_mul_of_nonneg_right hvL (pow_nonneg hv 3)
  have hp : 0 ≤ L * v ^ 3 := mul_nonneg (hv.trans hvL) (pow_nonneg hv 3)
  nlinarith only [hh, hp]

variable {ι : Type*} [Fintype ι]

/-- The coordinate energy kernel has its exact polynomial main term and an
  error proportional to v^2. This is uniform even for very small shifts. -/
theorem quadratic_difference_error (w a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L v E : ℝ) (hv : 0 ≤ v) (hvL : v ≤ L) (hE : 0 ≤ E)
    (hF : ∀ t ∈ Set.Icc 0 L, |cumulativeMass w a t - t| ≤ E) :
    |(∑ i, w i * (quadraticProfile L (a i) - quadraticProfile L (a i + v)) ^ 2) -
      ((4 / 3) * L ^ 3 * v ^ 2 - (2 / 3) * L ^ 2 * v ^ 3 - (2 / 15) * v ^ 5)| ≤
      8 * E * L ^ 2 * v ^ 2 := by
  have hh := weighted_profile_error w a ha L E (hv.trans hvL) (quadraticDifferenceSlope L v)
    (fun x => (quadraticProfile L x - quadraticProfile L (x + v)) ^ 2)
    (quadraticDifferenceSlope_integrable L v 0 L)
    (fun x hx => quadratic_difference_primitive L v x hv hvL hx) hF
  rw [integral_quadraticDifferenceSlope_mul L v hv hvL] at hh
  apply hh.trans
  have hvary := mul_le_mul_of_nonneg_left (quadraticDifference_variation_le L v hv hvL) hE
  nlinarith only [hvary]

#print axioms quadratic_difference_primitive
#print axioms integral_abs_quadraticDifferenceSlope
#print axioms quadratic_difference_error
end Erdos970.FiniteSelberg
