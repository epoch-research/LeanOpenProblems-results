import Submission.QuantitativeMonochromaticThreeAP
import Submission.QuadraticProgressionCurvature
import Submission.MaskedPhaseIncrement
import Submission.PolynomialMixedRecurrence

/-! Uniform simultaneous recurrence for linear and square-dilated unit phases,
with a bound polynomial in inverse accuracy for each fixed number of phases. -/
namespace Erdos3SimultaneousQuadraticRecurrence
open Finset Erdos3QuantitativeMonochromaticThreeAP Erdos3QuadraticProgressionCurvature
  Erdos3MaskedPhaseIncrement
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

lemma phaseLabel_close {V : Type*} (n : ℕ) (hn : 0 < n) (q : V → ℂ)
    (hq : ∀ x, ‖q x‖ ≤ 1) {x y : V} (he : phaseLabel n q hq x = phaseLabel n q hq y) :
    ‖q x-q y‖ ≤ 2/(n : ℝ) := by
  have hre := gridCoord_close hn ((Complex.abs_re_le_norm _).trans (hq x))
    ((Complex.abs_re_le_norm _).trans (hq y)) (congrArg Prod.fst he)
  have him := gridCoord_close hn ((Complex.abs_im_le_norm _).trans (hq x))
    ((Complex.abs_im_le_norm _).trans (hq y)) (congrArg Prod.snd he)
  calc
    _ ≤ |(q x-q y).re|+|(q x-q y).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1/(n : ℝ)+1/(n : ℝ) := by simpa only [Complex.sub_re,Complex.sub_im] using add_le_add hre him
    _ = _ := by ring

noncomputable def recurrenceBound (m t : ℕ) : ℕ :=
  Erdos3PolynomialMixedRecurrence.polynomialRecurrenceBound m t

/-- A single bounded positive d approximately annihilates all linear phases
and all square-dilated quadratic coefficients. The bound is uniform in the phases. -/
theorem simultaneous_mixed_recurrence {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℂ) (v : J → ℂ) (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ j, ‖v j‖ = 1) (t : ℕ) :
    ∃ d : ℕ, 0 < d ∧ d < recurrenceBound (Fintype.card I+Fintype.card J) t ∧
      (∀ i, ‖(w i)^d-1‖ ≤ (1/2 : ℝ)^t) ∧
      ∀ j, ‖(v j)^(d^2)-1‖ ≤ (1/2 : ℝ)^t := by
  exact Erdos3PolynomialMixedRecurrence.polynomial_mixed_recurrence w v hw hv t

/-- The square recurrence bound depends only on the number of phases and accuracy. -/
theorem simultaneous_square_recurrence {I : Type*} [Fintype I]
    (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1) (t : ℕ) :
    ∃ d : ℕ, 0 < d ∧ d < recurrenceBound (Fintype.card I) t ∧
      ∀ i, ‖(v i)^(d^2)-1‖ ≤ (1/2 : ℝ)^t := by
  obtain ⟨d,hd,hbound,_,hv'⟩ := simultaneous_mixed_recurrence
    (fun i : Empty ↦ nomatch i) v (fun i ↦ nomatch i) hv t
  exact ⟨d,hd,by simpa using hbound,hv'⟩

#print axioms simultaneous_mixed_recurrence
#print axioms simultaneous_square_recurrence
end Erdos3SimultaneousQuadraticRecurrence
