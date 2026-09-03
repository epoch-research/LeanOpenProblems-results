import Submission.SmoothCutoffTransfer

/-! Two-cutoff transfer for the squared shifted difference of a hard-cutoff
smooth profile. Both jumps are retained. -/
namespace Erdos970.FiniteSelberg
open Finset Real MeasureTheory
variable {ι : Type*} [Fintype ι]
set_option maxHeartbeats 1000000

lemma cutoffValue_square (L : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    cutoffValue L f x ^ 2 = cutoffValue L (fun t => f t ^ 2) x := by
  unfold cutoffValue
  split_ifs <;> simp

lemma cutoff_square_error (w a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L E B D : ℝ) (hL : 0 ≤ L) (hE : 0 ≤ E) (hB : 0 ≤ B) (hD0 : 0 ≤ D)
    (f df : ℝ → ℝ) (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hbound : ∀ x ∈ Set.Icc 0 L, |f x| ≤ B ∧ |df x| ≤ D)
    (hF : ∀ t ∈ Set.Icc 0 L, |cumulativeMass w a t - t| ≤ E) :
    |(∑ i, w i * cutoffValue L f (a i) ^ 2) - (∫ t in 0..L, f t ^ 2)| ≤
      E * (B ^ 2 + 2 * B * D * L) := by
  simp_rw [cutoffValue_square]
  apply cutoff_smooth_error w a ha L E (B ^ 2) (2 * B * D) hL hE
    (fun t => f t ^ 2) (fun t => 2 * f t * df t)
    (hf.pow 2) (by fun_prop)
  · intro x
    convert (hd x).pow 2 using 1 <;> simp
  · rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbound L ⟨hL, le_rfl⟩).1 2
  · intro x hx
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hh := mul_le_mul (hbound x hx).1 (hbound x hx).2 (abs_nonneg _) hB
    nlinarith only [hh]
  · exact hF

noncomputable def shiftCorrection (f : ℝ → ℝ) (v x : ℝ) : ℝ :=
  -2 * f x * f (x + v) + f (x + v) ^ 2

noncomputable def shiftCorrectionDerivative (f df : ℝ → ℝ) (v x : ℝ) : ℝ :=
  -2 * (df x * f (x + v) + f x * df (x + v)) + 2 * f (x + v) * df (x + v)

lemma shiftCorrection_hasDerivAt (f df : ℝ → ℝ) (v x : ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x) :
    HasDerivAt (shiftCorrection f v) (shiftCorrectionDerivative f df v x) x := by
  have hs : HasDerivAt (fun t => f (t + v)) (df (x + v)) x := by
    convert (hd (x + v)).comp x ((hasDerivAt_id x).add_const v) using 1 <;> simp
  convert (((hd x).mul hs).const_mul (-2)).add (hs.pow 2) using 1 <;>
    (try funext t) <;> dsimp [shiftCorrection, shiftCorrectionDerivative] <;> ring

lemma shiftCorrection_bounds (f df : ℝ → ℝ) (L v B D x : ℝ)
    (hv : 0 ≤ v) (hvL : v ≤ L) (hB : 0 ≤ B) (hD0 : 0 ≤ D)
    (hbound : ∀ x ∈ Set.Icc 0 L, |f x| ≤ B ∧ |df x| ≤ D)
    (hx : x ∈ Set.Icc 0 (L - v)) :
    |shiftCorrection f v x| ≤ 3 * B ^ 2 ∧
      |shiftCorrectionDerivative f df v x| ≤ 6 * B * D := by
  have hxL : x ∈ Set.Icc 0 L := ⟨hx.1, by linarith [hx.2]⟩
  have hxv : x + v ∈ Set.Icc 0 L := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hfx := (hbound x hxL).1
  have hdx := (hbound x hxL).2
  have hfv := (hbound (x + v) hxv).1
  have hdv := (hbound (x + v) hxv).2
  have hff : |f x| * |f (x + v)| ≤ B ^ 2 := by
    simpa only [pow_two] using mul_le_mul hfx hfv (abs_nonneg _) hB
  have hsq : |f (x + v)| ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hfv 2
  have hdf : |df x| * |f (x + v)| ≤ B * D := by
    simpa only [mul_comm B] using mul_le_mul hdx hfv (abs_nonneg _) hD0
  have hfd : |f x| * |df (x + v)| ≤ B * D := mul_le_mul hfx hdv (abs_nonneg _) hB
  have hfdv : |f (x + v)| * |df (x + v)| ≤ B * D := mul_le_mul hfv hdv (abs_nonneg _) hB
  constructor
  · unfold shiftCorrection
    apply (abs_add_le _ _).trans
    simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow]
    nlinarith only [hff, hsq]
  · unfold shiftCorrectionDerivative
    apply (abs_add_le _ _).trans
    simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hadd := abs_add_le (df x * f (x + v)) (f x * df (x + v))
    simp only [abs_mul] at hadd
    nlinarith only [hadd, hdf, hfd, hfdv]

lemma cutoff_difference_split (f : ℝ → ℝ) (L v x : ℝ) (hv : 0 ≤ v) :
    (cutoffValue L f x - cutoffValue L f (x + v)) ^ 2 =
      cutoffValue L (fun t => f t ^ 2) x + cutoffValue (L - v) (shiftCorrection f v) x := by
  unfold cutoffValue shiftCorrection
  by_cases hx : x < L
  · by_cases hxv : x + v < L
    · have hxc : x < L - v := by linarith
      simp only [if_pos hx, if_pos hxv, if_pos hxc]
      ring
    · have hxc : ¬x < L - v := by linarith
      simp only [if_pos hx, if_neg hxv, if_neg hxc]
      ring
  · have hxv : ¬x + v < L := by linarith
    have hxc : ¬x < L - v := by linarith
    simp only [if_neg hx, if_neg hxv, if_neg hxc, sub_self, zero_pow (by omega : 2 ≠ 0), add_zero]

lemma cutoff_difference_integral_split (f : ℝ → ℝ) (hf : Continuous f) (L v : ℝ) :
    (∫ t in 0..L, f t ^ 2) + (∫ t in 0..(L - v), shiftCorrection f v t) =
      (∫ t in 0..(L - v), (f t - f (t + v)) ^ 2) + (∫ t in (L - v)..L, f t ^ 2) := by
  have hs : Continuous (shiftCorrection f v) := by unfold shiftCorrection; fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hf.pow 2).intervalIntegrable 0 (L - v)) ((hf.pow 2).intervalIntegrable (L - v) L)
  have he : (∫ t in 0..(L - v), f t ^ 2) + (∫ t in 0..(L - v), shiftCorrection f v t) =
      ∫ t in 0..(L - v), (f t - f (t + v)) ^ 2 := by
    rw [← intervalIntegral.integral_add ((hf.pow 2).intervalIntegrable 0 (L - v))
      (hs.intervalIntegrable 0 (L - v))]
    apply intervalIntegral.integral_congr
    intro t ht
    unfold shiftCorrection
    ring
  linarith

/-- Both cutoffs enter the estimate. The error is uniform down to v=0 but
  need not vanish with v, which is appropriate for a discontinuous cutoff. -/
theorem cutoff_difference_error (w a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L v E B D : ℝ) (hv : 0 ≤ v) (hvL : v ≤ L) (hE : 0 ≤ E)
    (hB : 0 ≤ B) (hD0 : 0 ≤ D)
    (f df : ℝ → ℝ) (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hbound : ∀ x ∈ Set.Icc 0 L, |f x| ≤ B ∧ |df x| ≤ D)
    (hF : ∀ t ∈ Set.Icc 0 L, |cumulativeMass w a t - t| ≤ E) :
    |(∑ i, w i * (cutoffValue L f (a i) - cutoffValue L f (a i + v)) ^ 2) -
      ((∫ t in 0..(L - v), (f t - f (t + v)) ^ 2) + (∫ t in (L - v)..L, f t ^ 2))| ≤
      E * (4 * B ^ 2 + 8 * B * D * L) := by
  have hL : 0 ≤ L := hv.trans hvL
  have hc : 0 ≤ L - v := by linarith
  have hn := cutoff_square_error w a ha L E B D hL hE hB hD0 f df hf hdf hd hbound hF
  have hb := shiftCorrection_bounds f df L v B D (L - v) hv hvL hB hD0 hbound
  have hj := cutoff_smooth_error w a ha (L - v) E (3 * B ^ 2) (6 * B * D) hc hE
    (shiftCorrection f v) (shiftCorrectionDerivative f df v)
    (by unfold shiftCorrection; fun_prop)
    (by unfold shiftCorrectionDerivative; fun_prop)
    (shiftCorrection_hasDerivAt f df v · hd)
    ((hb ⟨hc, le_rfl⟩).1)
    (fun t ht => (shiftCorrection_bounds f df L v B D t hv hvL hB hD0 hbound ht).2)
    (fun t ht => hF t ⟨ht.1, by linarith [ht.2]⟩)
  simp_rw [cutoffValue_square] at hn
  simp_rw [cutoff_difference_split f L v _ hv, mul_add]
  rw [sum_add_distrib, ← cutoff_difference_integral_split f hf L v]
  have he (A B C D : ℝ) : A + B - (C + D) = (A - C) + (B - D) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  have hvprod : 0 ≤ E * B * D * v := by positivity
  nlinarith only [hn, hj, hvprod]

#print axioms cutoff_difference_error
end Erdos970.FiniteSelberg
