import Submission.CutoffSquareDifference
import Submission.HardCubicProfileCertificate

/-! Scaled hard-cubic profiles and their finite weighted norm and shift
estimates. The jumps are included through the two-cutoff transfer theorem. -/
namespace Erdos970.FiniteSelberg
open Finset Real MeasureTheory
set_option maxHeartbeats 2000000

noncomputable def scaledHardCubic (L x : ℝ) : ℝ :=
  10000 * L ^ 3 - 8866 * L ^ 2 * x + 5925 * L * x ^ 2 - 4667 * x ^ 3

noncomputable def scaledHardCubicDerivative (L x : ℝ) : ℝ :=
  -8866 * L ^ 2 + 11850 * L * x - 14001 * x ^ 2

noncomputable def hardCubicProfile (L x : ℝ) : ℝ := cutoffValue L (scaledHardCubic L) x

@[fun_prop] lemma scaledHardCubic_continuous (L : ℝ) : Continuous (scaledHardCubic L) := by
  unfold scaledHardCubic
  fun_prop

@[fun_prop] lemma scaledHardCubicDerivative_continuous (L : ℝ) :
    Continuous (scaledHardCubicDerivative L) := by
  unfold scaledHardCubicDerivative
  fun_prop

lemma scaledHardCubic_hasDerivAt (L x : ℝ) :
    HasDerivAt (scaledHardCubic L) (scaledHardCubicDerivative L x) x := by
  convert ((((hasDerivAt_const x (10000 * L ^ 3)).sub
    ((hasDerivAt_id x).const_mul (8866 * L ^ 2))).add
    (((hasDerivAt_id x).pow 2).const_mul (5925 * L))).sub
    (((hasDerivAt_id x).pow 3).const_mul 4667)) using 1 <;>
      (try funext t) <;> dsimp [scaledHardCubic, scaledHardCubicDerivative] <;> ring

lemma scaledHardCubic_nonneg (L x : ℝ) (hL : 0 ≤ L) (hx : 0 ≤ x) (hxL : x ≤ L) :
    0 ≤ scaledHardCubic L x := by
  have hq : 0 ≤ 7608 * L ^ 2 - 1258 * L * x + 4667 * x ^ 2 := by
    nlinarith [sq_nonneg (L - x)]
  have hp := mul_nonneg (sub_nonneg.mpr hxL) hq
  have hc : 0 ≤ 2392 * L ^ 3 := by positivity
  unfold scaledHardCubic
  nlinarith only [hp, hc]

lemma scaledHardCubic_le (L x : ℝ) (hx : 0 ≤ x) :
    scaledHardCubic L x ≤ 10000 * L ^ 3 := by
  have hq : 0 ≤ 8866 * L ^ 2 - 5925 * L * x + 4667 * x ^ 2 := by
    nlinarith [sq_nonneg (L - x)]
  have hp := mul_nonneg hx hq
  unfold scaledHardCubic
  nlinarith only [hp]

lemma scaledHardCubic_bounds (L x : ℝ) (hL : 0 ≤ L) (hx : x ∈ Set.Icc 0 L) :
    |scaledHardCubic L x| ≤ 10000 * L ^ 3 ∧
      |scaledHardCubicDerivative L x| ≤ 35000 * L ^ 2 := by
  constructor
  · rw [abs_of_nonneg (scaledHardCubic_nonneg L x hL hx.1 hx.2)]
    exact scaledHardCubic_le L x hx.1
  · have hn : scaledHardCubicDerivative L x ≤ 0 := by
      unfold scaledHardCubicDerivative
      nlinarith [sq_nonneg (L - x)]
    rw [abs_of_nonpos hn]
    have hx2 : x ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hx.1 hx.2 2
    have hLx : 0 ≤ L * x := mul_nonneg hL hx.1
    unfold scaledHardCubicDerivative
    nlinarith only [hx2, hLx, sq_nonneg L]

lemma hardCubicProfile_bounds (L x : ℝ) (hL : 0 ≤ L) (hx : 0 ≤ x) :
    0 ≤ hardCubicProfile L x ∧ hardCubicProfile L x ≤ 10000 * L ^ 3 := by
  unfold hardCubicProfile cutoffValue
  split_ifs with hxL
  · exact ⟨scaledHardCubic_nonneg L x hL hx hxL.le, scaledHardCubic_le L x hx⟩
  · constructor <;> positivity

private lemma integral_const_times_id (c a b : ℝ) :
    (∫ x in a..b, c * x) = c * ((b ^ 2 - a ^ 2) / 2) := by
  rw [intervalIntegral.integral_const_mul, integral_id]

lemma integral_scaledHardCubic_sq (L a b : ℝ) :
    (∫ x in a..b, scaledHardCubic L x ^ 2) =
      (21780889 / 7) * (b ^ 7 - a ^ 7) - 9217325 * L * (b ^ 6 - a ^ 6) +
      (117860869 / 5) * L ^ 2 * (b ^ 5 - a ^ 5) - 49600525 * L ^ 3 * (b ^ 4 - a ^ 4) +
      (197105956 / 3) * L ^ 4 * (b ^ 3 - a ^ 3) - 88660000 * L ^ 5 * (b ^ 2 - a ^ 2) +
      100000000 * L ^ 6 * (b - a) := by
  have he : (fun x => scaledHardCubic L x ^ 2) = fun x =>
      21780889 * x ^ 6 - (55303950 * L) * x ^ 5 + (117860869 * L ^ 2) * x ^ 4 -
      (198402100 * L ^ 3) * x ^ 3 + (197105956 * L ^ 4) * x ^ 2 -
      (177320000 * L ^ 5) * x + 100000000 * L ^ 6 := by
    funext x
    unfold scaledHardCubic
    ring
  rw [he]
  simp (discharger := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      integral_pow, integral_const_times_id, smul_eq_mul]
  norm_num
  ring

lemma scaledHardCubic_norm_integral (L : ℝ) :
    (∫ x in 0..L, scaledHardCubic L x ^ 2) = hardCubicNorm * L ^ 7 := by
  rw [integral_scaledHardCubic_sq, hardCubicNorm_eq]
  ring

lemma integral_scaledHardCubic_difference (L v a b : ℝ) :
    (∫ x in a..b, (scaledHardCubic L x - scaledHardCubic L (x + v)) ^ 2) =
      (196028001 * v ^ 2) * (b ^ 5 - a ^ 5) / 5 +
      (-331823700 * L * v ^ 2 + 392056002 * v ^ 3) * (b ^ 4 - a ^ 4) / 4 +
      (388688232 * L ^ 2 * v ^ 2 - 497735550 * L * v ^ 3 + 326713335 * v ^ 4) *
        (b ^ 3 - a ^ 3) / 3 +
      (-210124200 * L ^ 3 * v ^ 2 + 388688232 * L ^ 2 * v ^ 3 -
        276519750 * L * v ^ 4 + 130685334 * v ^ 5) * (b ^ 2 - a ^ 2) / 2 +
      (78605956 * L ^ 4 * v ^ 2 - 105062100 * L ^ 3 * v ^ 3 + 117860869 * L ^ 2 * v ^ 4 -
        55303950 * L * v ^ 5 + 21780889 * v ^ 6) * (b - a) := by
  have he : (fun x => (scaledHardCubic L x - scaledHardCubic L (x + v)) ^ 2) = fun x =>
      (196028001 * v ^ 2) * x ^ 4 +
      (-331823700 * L * v ^ 2 + 392056002 * v ^ 3) * x ^ 3 +
      (388688232 * L ^ 2 * v ^ 2 - 497735550 * L * v ^ 3 + 326713335 * v ^ 4) * x ^ 2 +
      (-210124200 * L ^ 3 * v ^ 2 + 388688232 * L ^ 2 * v ^ 3 -
        276519750 * L * v ^ 4 + 130685334 * v ^ 5) * x +
      (78605956 * L ^ 4 * v ^ 2 - 105062100 * L ^ 3 * v ^ 3 + 117860869 * L ^ 2 * v ^ 4 -
        55303950 * L * v ^ 5 + 21780889 * v ^ 6) := by
    funext x
    unfold scaledHardCubic
    ring
  rw [he]
  simp (discharger := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, integral_pow, integral_const_times_id, smul_eq_mul]
  norm_num
  ring

noncomputable def hardCubicShiftMain (L v : ℝ) : ℝ :=
  5721664 * L ^ 6 * v + (428544696 / 5) * L ^ 5 * v ^ 2 -
  (434463325 / 6) * L ^ 4 * v ^ 3 + 49600525 * L ^ 3 * v ^ 4 -
  (147536616 / 5) * L ^ 2 * v ^ 5 + 9217325 * L * v ^ 6 - (239589779 / 70) * v ^ 7

lemma scaledHardCubic_shift_integral (L v : ℝ) :
    (∫ x in 0..(L - v), (scaledHardCubic L x - scaledHardCubic L (x + v)) ^ 2) +
      (∫ x in (L - v)..L, scaledHardCubic L x ^ 2) = hardCubicShiftMain L v := by
  rw [integral_scaledHardCubic_difference, integral_scaledHardCubic_sq]
  unfold hardCubicShiftMain
  ring

lemma hardCubicShiftMain_self (L : ℝ) : hardCubicShiftMain L L = hardCubicNorm * L ^ 7 := by
  rw [hardCubicNorm_eq]
  unfold hardCubicShiftMain
  ring

variable {ι : Type*} [Fintype ι]

/-- The finite weighted squared norm has its exact leading coefficient and
  an absolute cumulative-discrepancy error of degree six. -/
theorem hardCubic_square_error (w a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L E : ℝ) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hF : ∀ t ∈ Set.Icc 0 L, |cumulativeMass w a t - t| ≤ E) :
    |(∑ i, w i * hardCubicProfile L (a i) ^ 2) - hardCubicNorm * L ^ 7| ≤
      800000000 * E * L ^ 6 := by
  have hh := cutoff_square_error w a ha L E (10000 * L ^ 3) (35000 * L ^ 2)
    hL hE (by positivity) (by positivity) (scaledHardCubic L) (scaledHardCubicDerivative L)
    (scaledHardCubic_continuous L) (scaledHardCubicDerivative_continuous L)
    (scaledHardCubic_hasDerivAt L) (fun x hx => scaledHardCubic_bounds L x hL hx) hF
  rw [scaledHardCubic_norm_integral] at hh
  convert hh using 1 <;> dsimp [hardCubicProfile] <;> ring

/-- Uniform weighted transfer for the squared shifted difference, including
  the two jumps at L-v and L. -/
theorem hardCubic_difference_error (w a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L v E : ℝ) (hv : 0 ≤ v) (hvL : v ≤ L) (hE : 0 ≤ E)
    (hF : ∀ t ∈ Set.Icc 0 L, |cumulativeMass w a t - t| ≤ E) :
    |(∑ i, w i * (hardCubicProfile L (a i) - hardCubicProfile L (a i + v)) ^ 2) -
      hardCubicShiftMain L v| ≤ 3200000000 * E * L ^ 6 := by
  have hL := hv.trans hvL
  have hh := cutoff_difference_error w a ha L v E (10000 * L ^ 3) (35000 * L ^ 2)
    hv hvL hE (by positivity) (by positivity) (scaledHardCubic L) (scaledHardCubicDerivative L)
    (scaledHardCubic_continuous L) (scaledHardCubicDerivative_continuous L)
    (scaledHardCubic_hasDerivAt L) (fun x hx => scaledHardCubic_bounds L x hL hx) hF
  rw [scaledHardCubic_shift_integral] at hh
  convert hh using 1 <;> dsimp [hardCubicProfile] <;> ring

#print axioms hardCubic_square_error
#print axioms hardCubic_difference_error
end Erdos970.FiniteSelberg
