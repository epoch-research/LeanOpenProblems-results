import Submission.CumulativeVariation

/-! Layer-cake estimates for the truncated quadratic logarithmic profile.
This is analytic infrastructure, not a quadratic Jacobsthal bound. -/
namespace Erdos970.FiniteSelberg
open Finset Real MeasureTheory

noncomputable def quadraticProfile (L x : ℝ) : ℝ := max (L ^ 2 - x ^ 2) 0

def quadraticSlope (L t : ℝ) : ℝ := 4 * L ^ 2 * t - 4 * t ^ 3

@[fun_prop] lemma quadraticSlope_continuous (L : ℝ) : Continuous (quadraticSlope L) := by
  unfold quadraticSlope
  fun_prop

lemma integral_quadraticSlope (L a b : ℝ) :
    (∫ t in a..b, quadraticSlope L t) =
      2 * L ^ 2 * (b ^ 2 - a ^ 2) - (b ^ 4 - a ^ 4) := by
  unfold quadraticSlope
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_id, integral_pow]
    norm_num
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

lemma integral_quadraticSlope_mul (L a b : ℝ) :
    (∫ t in a..b, quadraticSlope L t * t) =
      (4 / 3) * L ^ 2 * (b ^ 3 - a ^ 3) - (4 / 5) * (b ^ 5 - a ^ 5) := by
  have he : (fun t => quadraticSlope L t * t) =
      fun t => (4 * L ^ 2) * t ^ 2 - 4 * t ^ 4 := by
    funext t
    unfold quadraticSlope
    ring
  rw [he, intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow, integral_pow]
    norm_num
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

lemma quadraticSlope_nonneg (L t : ℝ) (ht : 0 ≤ t) (htL : t ≤ L) :
    0 ≤ quadraticSlope L t := by
  have hsq : 0 ≤ L ^ 2 - t ^ 2 := by nlinarith
  have hh := mul_nonneg (show 0 ≤ 4 * t by positivity) hsq
  unfold quadraticSlope
  nlinarith only [hh]

lemma quadratic_square_primitive (L x : ℝ) (hL : 0 ≤ L) (hx : 0 ≤ x) :
    quadraticProfile L x ^ 2 =
      if x ≤ L then (∫ t in x..L, quadraticSlope L t) else 0 := by
  by_cases hxL : x ≤ L
  · rw [if_pos hxL, quadraticProfile, max_eq_left (by nlinarith : 0 ≤ L ^ 2 - x ^ 2),
      integral_quadraticSlope]
    ring
  · rw [if_neg hxL, quadraticProfile, max_eq_right (by nlinarith : L ^ 2 - x ^ 2 ≤ 0)]
    norm_num

lemma integral_abs_quadraticSlope (L : ℝ) (hL : 0 ≤ L) :
    (∫ t in 0..L, |quadraticSlope L t|) = L ^ 4 := by
  have he : (∫ t in 0..L, |quadraticSlope L t|) = ∫ t in 0..L, quadraticSlope L t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hL] at ht
    exact abs_of_nonneg (quadraticSlope_nonneg L t ht.1 ht.2)
  rw [he, integral_quadraticSlope]
  ring

variable {ι : Type*} [Fintype ι]

/-- The square mass has leading coefficient8/15 and a variation error of orderL^4. -/
theorem quadratic_square_error (w a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L E : ℝ) (hL : 0 ≤ L)
    (hF : ∀ t ∈ Set.Icc 0 L, |cumulativeMass w a t - t| ≤ E) :
    |(∑ i, w i * quadraticProfile L (a i) ^ 2) - (8 / 15) * L ^ 5| ≤ E * L ^ 4 := by
  have hh := weighted_profile_error w a ha L E hL (quadraticSlope L)
    (fun x => quadraticProfile L x ^ 2) ((quadraticSlope_continuous L).intervalIntegrable _ _)
    (fun x hx => quadratic_square_primitive L x hL hx) hF
  rw [integral_abs_quadraticSlope L hL, integral_quadraticSlope_mul] at hh
  convert hh using 1 <;> ring

/-- The one-sided lower mass estimate only needs a lower cumulative bound. -/
theorem quadratic_square_lower (w a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L E : ℝ) (hL : 0 ≤ L)
    (hF : ∀ t ∈ Set.Icc 0 L, t - E ≤ cumulativeMass w a t) :
    (8 / 15) * L ^ 5 - E * L ^ 4 ≤ ∑ i, w i * quadraticProfile L (a i) ^ 2 := by
  have hg : IntervalIntegrable (quadraticSlope L) volume 0 L :=
    (quadraticSlope_continuous L).intervalIntegrable 0 L
  rw [weighted_profile_integral w a ha L hL (quadraticSlope L)
    (fun x => quadraticProfile L x ^ 2) hg (fun x hx => quadratic_square_primitive L x hL hx)]
  have hh := intervalIntegral.integral_mono_on hL
    ((by fun_prop : Continuous (fun t => quadraticSlope L t * (t - E))).intervalIntegrable 0 L)
    (cumulative_mul_integrable w a _ _ _ hg)
    (fun t ht => mul_le_mul_of_nonneg_left (hF t ht) (quadraticSlope_nonneg L t ht.1 ht.2))
  have he : (∫ t in 0..L, quadraticSlope L t * (t - E)) =
      (8 / 15) * L ^ 5 - E * L ^ 4 := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_mul_const,
      integral_quadraticSlope_mul, integral_quadraticSlope]
    · ring
    all_goals apply Continuous.intervalIntegrable; fun_prop
  rwa [he] at hh

#print axioms quadratic_square_error
#print axioms quadratic_square_lower
end Erdos970.FiniteSelberg
