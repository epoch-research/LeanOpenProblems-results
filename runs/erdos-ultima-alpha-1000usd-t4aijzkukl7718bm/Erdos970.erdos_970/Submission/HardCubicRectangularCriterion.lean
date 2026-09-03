import Submission.HardCubicSurvivorCount
import Submission.RectangularVarianceTransfer

/-! The unrestricted hard-cubic long-interval count supplies the count input
in the rectangular transfer. The remaining row-variance input is uniform in
phase and remains an explicit hypothesis. -/
namespace Erdos970.GapAverages
open Finset Real FiniteSelberg

noncomputable def hardCubicCountDenominator (t : ℕ) : ℝ :=
  800000000 * log ((hardCubicCutoffScale * t ^ 3 : ℕ) : ℝ)

lemma hardCubicCountDenominator_pos (t : ℕ) (ht : 0 < t) :
    0 < hardCubicCountDenominator t := by
  have ht3 : 1 ≤ t ^ 3 := one_le_pow₀ ht
  have hh := Nat.mul_le_mul_left hardCubicCutoffScale ht3
  have hR : 1 < hardCubicCutoffScale * t ^ 3 := by
    have hD := hardCubicCutoffScale_ge
    nlinarith only [hh, hD]
  exact mul_pos (by norm_num) (log_pos (by exact_mod_cast hR))

lemma hardCubic_rectangle_mean_lower (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (t : ℕ) (ht : 0 < t) (hcard : P.card ≤ t ^ 4) (n p : ℕ)
    (hm : 2 * hardCubicBoundConstant * (t : ℝ) ^ 10 ≤ (p * n : ℕ)) :
    ∀ r : Phase P, (p : ℝ) * ((n : ℝ) / hardCubicCountDenominator t) ≤ intervalCount P (p * n) r := by
  intro r
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (hardCubicCountDenominator_pos t ht)).mpr
  have hh := phase_count_three_quarters P hP t ht hcard (p * n) hm r
  simpa only [Nat.cast_mul, hardCubicCountDenominator, mul_comm] using hh

/-- A short low-count phase necessarily produces an unusually large row
variance after its affine dilation into a sufficiently long rectangle. -/
theorem low_count_forces_large_row_variance (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (t : ℕ) (ht : 0 < t) (hcard : P.card ≤ t ^ 4) (n p : ℕ) (hp : 0 < p)
    (hc : ∀ q ∈ P, p.Coprime q)
    (hm : 2 * hardCubicBoundConstant * (t : ℝ) ^ 10 ≤ (p * n : ℕ))
    (b : ℝ) (hb : b ≤ (n : ℝ) / hardCubicCountDenominator t)
    (r : Phase P) (hr : intervalCount P n r ≤ b) :
    ((n : ℝ) / hardCubicCountDenominator t - b) ^ 2 ≤
      (p : ℝ) * rowConditionalVariance P (p * n) p (affinePhaseEquiv P hP 0 p hc r) := by
  let s := affinePhaseEquiv P hP 0 p hc r
  have hA : (n : ℝ) / hardCubicCountDenominator t ≤ intervalCount P (p * n) s / p := by
    apply (le_div_iff₀ (show (0 : ℝ) < p by exact_mod_cast hp)).mpr
    simpa only [mul_comm] using hardCubic_rectangle_mean_lower P hP t ht hcard n p hm s
  by_contra hbad
  have hgap := lt_of_not_ge hbad
  have hh := row_gt_of_mean_variance P (p * n) p hp s ⟨0, hp⟩
    ((n : ℝ) / hardCubicCountDenominator t) b (rowConditionalVariance P (p * n) p s)
    hA hb le_rfl hgap
  rw [row_zero_affine_rectangle P hP n p hp hc] at hh
  exact hh.not_ge hr

/-- Uniform variance control below the displayed gap would give every
short phase more than b survivors. The variance control is not assumed as an
axiom and has not been proved by the phase-averaged variance estimate. -/
theorem count_lower_of_hardCubic_rectangular_variance (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (t : ℕ) (ht : 0 < t) (hcard : P.card ≤ t ^ 4)
    (n p : ℕ) (hp : 0 < p) (hc : ∀ q ∈ P, p.Coprime q)
    (hm : 2 * hardCubicBoundConstant * (t : ℝ) ^ 10 ≤ (p * n : ℕ))
    (b V : ℝ) (hb : b ≤ (n : ℝ) / hardCubicCountDenominator t)
    (hvar : ∀ r : Phase P, rowConditionalVariance P (p * n) p r ≤ V)
    (hgap : (p : ℝ) * V < ((n : ℝ) / hardCubicCountDenominator t - b) ^ 2) :
    ∀ r : Phase P, b < intervalCount P n r := by
  apply count_lower_of_rectangular_variance P hP n p hp hc
    ((n : ℝ) / hardCubicCountDenominator t) b V hb
    (hardCubic_rectangle_mean_lower P hP t ht hcard n p hm) hvar hgap

#print axioms low_count_forces_large_row_variance
#print axioms count_lower_of_hardCubic_rectangular_variance
end Erdos970.GapAverages
