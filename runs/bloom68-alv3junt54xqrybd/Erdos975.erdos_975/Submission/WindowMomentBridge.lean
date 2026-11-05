import FormalConjecturesUtil

/-!
# Persistence costs for centered moving-window moments

A nonnegative discrepancy gap on a measurable set costs its `k`th power
multiplied by the measure of the set in the global absolute `k`th moment.
For a count family whose mean is `Y * H`, containment in slightly enlarged
windows loses exactly `η * Y * H`; containment of slightly shortened windows
has the same loss for a deficit.

These are analytic supporting lemmas. The window-containment hypotheses must
be proved separately for the chosen point process. In particular, this file
does not assert persistence at the *same* window width, an arithmetic moment
bound, or a polynomial divisor asymptotic.
-/

namespace Erdos975Support

open MeasureTheory
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- An absolute gap on a measurable set gives a lower bound for the global
absolute moment. Integrability is explicit, so a nonintegrable Bochner
integral cannot silently be used as zero. -/
theorem persistent_gap_moment_le {μ : Measure Ω} {D : Ω → ℝ} {E : Set Ω}
    {A : ℝ} {k : ℕ} (hE : MeasurableSet E) (hμE : μ E ≠ ∞)
    (hA : 0 ≤ A) (hD : ∀ t ∈ E, A ≤ |D t|)
    (hint : Integrable (fun t ↦ |D t| ^ k) μ) :
    A ^ k * μ.real E ≤ ∫ t, |D t| ^ k ∂μ := by
  have hlocal : A ^ k * μ.real E ≤ ∫ t in E, |D t| ^ k ∂μ := by
    apply setIntegral_ge_of_const_le_real hE hμE
    · intro t ht
      exact pow_le_pow_left₀ hA (hD t ht) k
    · exact hint.integrableOn
  exact hlocal.trans (setIntegral_le_integral hint
    (Filter.Eventually.of_forall fun t ↦ pow_nonneg (abs_nonneg (D t)) k))

/-- A fixed-target excess persists in an enlarged-window count on every
location where the enlarged window contains the target window. The loss in
the centered gap is exactly the additional mean `η * Y * H`. -/
theorem enlarged_window_excess_cost {μ : Measure Ω} {C : ℝ → Ω → ℝ}
    {E : Set Ω} {t₀ : Ω} {Y H η A : ℝ} {k : ℕ}
    (hE : MeasurableSet E) (hμE : μ E ≠ ∞)
    (hgap : η * Y * H ≤ A)
    (hexcess : A ≤ C Y t₀ - Y * H)
    (hcontain : ∀ t ∈ E, C Y t₀ ≤ C ((1 + η) * Y) t)
    (hint : Integrable
      (fun t ↦ |C ((1 + η) * Y) t - ((1 + η) * Y) * H| ^ k) μ) :
    (A - η * Y * H) ^ k * μ.real E ≤
      ∫ t, |C ((1 + η) * Y) t - ((1 + η) * Y) * H| ^ k ∂μ := by
  apply persistent_gap_moment_le hE hμE (sub_nonneg.mpr hgap) _ hint
  intro t ht
  have hc := hcontain t ht
  have hp : A - η * Y * H ≤
      C ((1 + η) * Y) t - ((1 + η) * Y) * H := by
    nlinarith
  exact hp.trans (le_abs_self _)

/-- A fixed-target deficit persists in shortened-window counts whenever
those windows are contained in the target window. The same additional-mean
loss as for an excess occurs, with the opposite discrepancy sign. -/
theorem shortened_window_deficit_cost {μ : Measure Ω} {C : ℝ → Ω → ℝ}
    {E : Set Ω} {t₀ : Ω} {Y H η A : ℝ} {k : ℕ}
    (hE : MeasurableSet E) (hμE : μ E ≠ ∞)
    (hgap : η * Y * H ≤ A)
    (hdeficit : A ≤ Y * H - C Y t₀)
    (hcontain : ∀ t ∈ E, C ((1 - η) * Y) t ≤ C Y t₀)
    (hint : Integrable
      (fun t ↦ |C ((1 - η) * Y) t - ((1 - η) * Y) * H| ^ k) μ) :
    (A - η * Y * H) ^ k * μ.real E ≤
      ∫ t, |C ((1 - η) * Y) t - ((1 - η) * Y) * H| ^ k ∂μ := by
  apply persistent_gap_moment_le hE hμE (sub_nonneg.mpr hgap) _ hint
  intro t ht
  have hc := hcontain t ht
  have hp : A - η * Y * H ≤
      -(C ((1 - η) * Y) t - ((1 - η) * Y) * H) := by
    nlinarith
  exact hp.trans (neg_le_abs _)

end Erdos975Support
