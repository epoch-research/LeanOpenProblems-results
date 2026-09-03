import Submission.JumpProfileTransfer

/-! Cumulative discrepancy controls a smooth function with a hard cutoff.
The endpoint jump is retained, not treated as a zero-measure atom of the
finite weighted distribution. -/
namespace Erdos970.FiniteSelberg
open Finset Real MeasureTheory
variable {ι : Type*} [Fintype ι]

noncomputable def cutoffValue (L : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < L then f x else 0

lemma cutoffValue_eq_jumpProfile (L : ℝ) (f df : ℝ → ℝ)
    (hdf : Continuous df) (hd : ∀ x, HasDerivAt f (df x) x) :
    cutoffValue L f = jumpProfile L (f L) (fun x => -df x) := by
  funext x
  unfold cutoffValue jumpProfile
  split_ifs
  · rw [intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hdf.intervalIntegrable x L)]
    ring
  · rfl

lemma cutoff_smooth_main (L : ℝ) (f df : ℝ → ℝ) (hf : Continuous f)
    (hdf : Continuous df) (hd : ∀ x, HasDerivAt f (df x) x) :
    f L * L + (∫ t in 0..L, -df t * t) = ∫ t in 0..L, f t := by
  have hdprod (x : ℝ) : HasDerivAt (fun t => t * f t) (f x + x * df x) x := by
    convert (hasDerivAt_id x).mul (hd x) using 1 <;> simp [id_eq]
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc 0 L) => hdprod t)
    ((hf.add (continuous_id.mul hdf)).intervalIntegrable 0 L)
  rw [intervalIntegral.integral_add (f := f) (g := fun t => t * df t) (hf.intervalIntegrable 0 L)
    ((continuous_id.mul hdf).intervalIntegrable 0 L)] at hh
  have he : (fun t => -df t * t) = fun t => -(t * df t) := by funext t; ring
  rw [he, intervalIntegral.integral_neg]
  simp only [zero_mul] at hh
  linarith

/-- A simple derivative-supremum version of the total-variation estimate.
There is no positivity requirement on f or the finite weights. -/
theorem cutoff_smooth_error (w a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L E M D : ℝ) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (f df : ℝ → ℝ) (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hM : |f L| ≤ M) (hD : ∀ x ∈ Set.Icc 0 L, |df x| ≤ D)
    (hF : ∀ t ∈ Set.Icc 0 L, |cumulativeMass w a t - t| ≤ E) :
    |(∑ i, w i * cutoffValue L f (a i)) - (∫ t in 0..L, f t)| ≤ E * (M + D * L) := by
  rw [cutoffValue_eq_jumpProfile L f df hdf hd]
  have hh := weighted_jump_error w a ha L (f L) E hL (fun t => -df t)
    (hdf.neg.intervalIntegrable 0 L) hF
  rw [cutoff_smooth_main L f df hf hdf hd] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hE
  have hi : (∫ t in 0..L, |-df t|) ≤ D * L := by
    calc
      _ ≤ ∫ _t in (0 : ℝ)..L, D := by
        apply intervalIntegral.integral_mono_on hL (hdf.neg.abs.intervalIntegrable 0 L)
          (continuous_const.intervalIntegrable 0 L)
        intro t ht
        simpa only [abs_neg] using hD t ht
      _ = D * L := by rw [intervalIntegral.integral_const]; simp [smul_eq_mul, mul_comm]
  exact add_le_add hM hi

#print axioms cutoff_smooth_error
end Erdos970.FiniteSelberg
