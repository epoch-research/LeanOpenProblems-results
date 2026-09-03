import Submission.FiniteLayerCake

/-!
Finite weighted integration by parts and a total-variation error bound.
In particular, approximate uniform cumulative mass controls polynomial moments
of every degree. These lemmas do not assert a quadratic Jacobsthal estimate.
-/
namespace Erdos970.FiniteSelberg
open Finset Real MeasureTheory
variable {ι : Type*} [Fintype ι]

lemma integral_general_cut (g : ℝ → ℝ) (a L : ℝ) (hL : 0 ≤ L) (ha : 0 ≤ a) :
    (∫ t in 0..L, if a < t then g t else 0) =
      if a ≤ L then (∫ t in a..L, g t) else 0 := by
  rw [intervalIntegral.integral_of_le hL]
  change (∫ t in Set.Ioc 0 L, (Set.Ioi a).indicator g t) = _
  rw [MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.inter_comm, Set.Ioc_inter_Ioi,
    max_eq_right ha]
  by_cases h : a ≤ L
  · rw [if_pos h, intervalIntegral.integral_of_le h]
  · rw [if_neg h, Set.Ioc_eq_empty_of_le (le_of_not_ge h), setIntegral_empty]

lemma cumulative_mul_integrable (w a : ι → ℝ) (g : ℝ → ℝ) (c L : ℝ)
    (hg : IntervalIntegrable g volume c L) :
    IntervalIntegrable (fun t => g t * cumulativeMass w a t) volume c L := by
  have he : (fun t => g t * cumulativeMass w a t) =
      fun t => ∑ i, w i * (if a i < t then g t else 0) := by
    funext t
    simp only [cumulativeMass, mul_sum]
    apply sum_congr rfl
    intro i hi
    split_ifs <;> ring
  rw [he]
  have hh := IntervalIntegrable.sum univ (fun i (_ : i ∈ (univ : Finset ι)) =>
    (intervalIntegrable_cut hg (a i)).const_mul (w i))
  simpa only [sum_fn] using hh

/-- Integration against a finite cumulative mass, including atoms outside the
  support interval. No sign restriction on the weights or the integrand is used. -/
theorem weighted_profile_integral (w a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L : ℝ) (hL : 0 ≤ L) (g f : ℝ → ℝ)
    (hg : IntervalIntegrable g volume 0 L)
    (hf : ∀ x, 0 ≤ x → f x = if x ≤ L then (∫ t in x..L, g t) else 0) :
    (∑ i, w i * f (a i)) = ∫ t in 0..L, g t * cumulativeMass w a t := by
  have he : (fun t => g t * cumulativeMass w a t) =
      fun t => ∑ i, w i * (if a i < t then g t else 0) := by
    funext t
    simp only [cumulativeMass, mul_sum]
    apply sum_congr rfl
    intro i hi
    split_ifs <;> ring
  rw [he, intervalIntegral.integral_finset_sum]
  · apply sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_const_mul, integral_general_cut g (a i) L hL (ha i),
      hf (a i) (ha i)]
  · intro i hi
    exact (intervalIntegrable_cut hg (a i)).const_mul (w i)

/-- The cumulative error is multiplied by the total variation of the profile,
  rather than by the sizes of its individual polynomial coefficients. -/
theorem cumulative_integral_error (w a : ι → ℝ) (L E : ℝ) (hL : 0 ≤ L)
    (g : ℝ → ℝ) (hg : IntervalIntegrable g volume 0 L)
    (hF : ∀ t ∈ Set.Icc 0 L, |cumulativeMass w a t - t| ≤ E) :
    |(∫ t in 0..L, g t * cumulativeMass w a t) - (∫ t in 0..L, g t * t)| ≤
      E * (∫ t in 0..L, |g t|) := by
  have hgA := cumulative_mul_integrable w a g 0 L hg
  have hgt : IntervalIntegrable (fun t => g t * t) volume 0 L :=
    hg.mul_continuousOn continuous_id.continuousOn
  rw [← intervalIntegral.integral_sub hgA hgt]
  have he : (fun t => g t * cumulativeMass w a t - g t * t) =
      fun t => g t * (cumulativeMass w a t - t) := by funext t; ring
  rw [he]
  apply (intervalIntegral.abs_integral_le_integral_abs hL).trans
  have hi : IntervalIntegrable (fun t => g t * (cumulativeMass w a t - t)) volume 0 L := by
    simpa only [mul_sub] using hgA.sub hgt
  calc
    _ ≤ ∫ t in 0..L, E * |g t| := by
      apply intervalIntegral.integral_mono_on hL hi.abs (hg.abs.const_mul E)
      intro t ht
      rw [abs_mul, mul_comm E]
      exact mul_le_mul_of_nonneg_left (hF t ht) (abs_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- A useful packaged form for continuous or piecewise-polynomial profiles. -/
theorem weighted_profile_error (w a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L E : ℝ) (hL : 0 ≤ L) (g f : ℝ → ℝ)
    (hg : IntervalIntegrable g volume 0 L)
    (hf : ∀ x, 0 ≤ x → f x = if x ≤ L then (∫ t in x..L, g t) else 0)
    (hF : ∀ t ∈ Set.Icc 0 L, |cumulativeMass w a t - t| ≤ E) :
    |(∑ i, w i * f (a i)) - (∫ t in 0..L, g t * t)| ≤
      E * (∫ t in 0..L, |g t|) := by
  rw [weighted_profile_integral w a ha L hL g f hg hf]
  exact cumulative_integral_error w a L E hL g hg hF

lemma integral_nat_power_derivative (n : ℕ) (a L : ℝ) :
    (∫ t in a..L, ((n : ℝ) + 1) * t ^ n) = L ^ (n + 1) - a ^ (n + 1) := by
  rw [intervalIntegral.integral_const_mul, integral_pow]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Every moment has its sharp leading coefficient, with a uniform lower-order
  error. The degree here is arbitrary, not restricted to one or two. -/
theorem cumulative_power_moment (w a : ι → ℝ) (L E : ℝ) (hL : 0 ≤ L)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ L)
    (htotal : |(∑ i, w i) - L| ≤ E)
    (hF : ∀ t ∈ Set.Icc 0 L, |cumulativeMass w a t - t| ≤ E) (n : ℕ) :
    |(∑ i, w i * a i ^ (n + 1)) - L ^ (n + 2) / ((n : ℝ) + 2)| ≤
      2 * E * L ^ (n + 1) := by
  let g : ℝ → ℝ := fun t => ((n : ℝ) + 1) * t ^ n
  have hg : IntervalIntegrable g volume 0 L := (by fun_prop : Continuous g).intervalIntegrable _ _
  have hint : (∫ t in 0..L, |g t|) = L ^ (n + 1) := by
    have he : (∫ t in 0..L, |g t|) = ∫ t in 0..L, g t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hL] at ht
      exact abs_of_nonneg (mul_nonneg (by positivity) (pow_nonneg ht.1 _))
    rw [he, integral_nat_power_derivative]
    simp
  have hmain : (∫ t in 0..L, g t * t) =
      ((n : ℝ) + 1) * L ^ (n + 2) / ((n : ℝ) + 2) := by
    have he : (fun t => g t * t) = fun t => ((n : ℝ) + 1) * t ^ (n + 1) := by
      funext t
      dsimp only [g]
      rw [pow_succ]
      ring
    rw [he, intervalIntegral.integral_const_mul, integral_pow]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, zero_pow (by omega : n + 1 + 1 ≠ 0), sub_zero]
    ring
  have hid : (∫ t in 0..L, g t * cumulativeMass w a t) =
      L ^ (n + 1) * (∑ i, w i) - ∑ i, w i * a i ^ (n + 1) := by
    have hf (x : ℝ) (hx : 0 ≤ x) :
        (if x ≤ L then L ^ (n + 1) - x ^ (n + 1) else 0) =
          if x ≤ L then (∫ t in x..L, g t) else 0 := by
      rw [integral_nat_power_derivative]
    rw [← weighted_profile_integral w a (fun i => (ha i).1) L hL g
      (fun x => if x ≤ L then L ^ (n + 1) - x ^ (n + 1) else 0) hg hf]
    simp_rw [if_pos (ha _).2, mul_sub]
    rw [sum_sub_distrib]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  have herr := cumulative_integral_error w a L E hL g hg hF
  rw [hint, hmain, hid] at herr
  have htotal' := mul_le_mul_of_nonneg_left htotal (pow_nonneg hL (n + 1))
  have he : (∑ i, w i * a i ^ (n + 1)) - L ^ (n + 2) / ((n : ℝ) + 2) =
      L ^ (n + 1) * ((∑ i, w i) - L) -
        (L ^ (n + 1) * (∑ i, w i) - (∑ i, w i * a i ^ (n + 1)) -
          ((n : ℝ) + 1) * L ^ (n + 2) / ((n : ℝ) + 2)) := by
    have hn : (n : ℝ) + 2 ≠ 0 := by positivity
    rw [show n + 2 = (n + 1) + 1 from by omega, pow_succ]
    field_simp
    ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg (pow_nonneg hL (n + 1))]
  nlinarith only [htotal', herr]

#print axioms weighted_profile_error
#print axioms cumulative_power_moment
end Erdos970.FiniteSelberg
