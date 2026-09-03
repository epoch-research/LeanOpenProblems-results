import Submission.LambertLinearPhaseThreshold
import Submission.LambertRawHankelNonsingular

/-!
A linear starting-index bound for real-weight Lambert detection and raw
Hankel nonsingularity. This is auxiliary analysis, not a settlement of Erdos 68.
-/

namespace LambertLinearHankel

open Finset LambertDifferenceOperators LambertRawBounds LambertTailRows
  LambertSharperOperatorBounds FactorialGeometricProductBound
  LambertCyclicRowLowerBound LambertCyclicCombinationLowerBound
  LambertLongBoundedCombinations LambertCyclicMass LambertPhaseMassBounds
  LambertUniformRawNonvanishing LambertLinearPhaseThreshold
  LambertRawHankelNonsingular

noncomputable section

variable (d : ℕ) [NeZero d]

lemma weighted_window_bound_real (H : ℕ) (w : ZMod d → ℝ)
    (r : ℕ → ℝ) (B : ℝ)
    (hr : ∀ j : ZMod d,
      (∑ h ∈ Finset.range d, rate d^(H+j.val+h)*|r (H+j.val+h)|) ≤ B) :
    (∑ h ∈ Finset.range d, rate d^(H+h)*
      |∑ j : ZMod d, w j*r (H+h+j.val)|) ≤
      mass (weightedCoefficients d w)*B := by
  have hp := rate_pos d
  calc
    _ ≤ ∑ h ∈ Finset.range d, ∑ j : ZMod d,
        (|w j|/rate d^j.val)*(rate d^(H+j.val+h)*|r (H+j.val+h)|) := by
      apply Finset.sum_le_sum
      intro h _
      apply (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _)
        (pow_nonneg hp.le _)).trans_eq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [show H+j.val+h=(H+h)+j.val by omega, abs_mul]
      simp only [pow_add]
      field_simp
    _ = ∑ j : ZMod d, (|w j|/rate d^j.val)*
        (∑ h ∈ Finset.range d, rate d^(H+j.val+h)*|r (H+j.val+h)|) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intros
      exact (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ j : ZMod d, (|w j|/rate d^j.val)*B := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hr j) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      unfold mass weightedCoefficients
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_div, abs_of_pos (pow_pos hp _)]

lemma first_window_lower_real (H : ℕ) (w : ZMod d → ℝ) (hd : 12 ≤ d) :
    Real.exp (-48)*mass (weightedCoefficients d w)/(rate d+1) ≤
      ∑ h ∈ Finset.range d, rate d^(H+h)*
        |∑ j : ZMod d, w j*
          rawApply (List.range' 2 (d-2)) (geometricRowTail d) (H+h+j.val)| := by
  have hp := rate_pos d
  have he : (∑ h ∈ Finset.range d, rate d^(H+h)*
      |∑ j : ZMod d, w j*
        rawApply (List.range' 2 (d-2)) (geometricRowTail d) (H+h+j.val)|) =
      mass (cyclicApply d (List.range' 2 (d-2))
        (convolve d (weightedCoefficients d w) (rowModel d))) := by
    rw [← phase_sum_eq_mass d H]
    apply Finset.sum_congr rfl
    intro h _
    have hm := combined_raw_model d (List.range' 2 (d-2))
      (geometricRowTail d) (rowModel d)
      (geometricRowTail_model d (by omega)) w (H+h)
    have ha := congrArg abs hm
    simpa only [abs_mul, abs_of_pos (pow_pos hp _)] using ha
  rw [he]
  exact first_row_mass_lower d (d-2) hd (by omega) _

/-- No integrality or height restriction is imposed on these d weights. -/
theorem real_weight_detection (H : ℕ) (w : ZMod d → ℝ)
    (hd : 12 ≤ d) (hH : 420*d ≤ H) (hw : w ≠ 0) :
    ∃ n, H ≤ n ∧ n < H+d ∧
      (∑ j : ZMod d, w j*rawTail (d-2) (n+j.val)) ≠ 0 := by
  classical
  have hp := rate_pos d
  have hc : 0 < mass (weightedCoefficients d w) :=
    lt_of_lt_of_le (norm_pos_iff.mpr (weightedCoefficients_ne_zero d w hw))
      (norm_le_mass _)
  let r : ℕ → ℝ := fun n => ∑' k : ℕ,
    rawApply (List.range' 2 (d-2)) (geometricRowTail (k+d+1)) n
  have hr (j : ZMod d) :
      (∑ h ∈ Finset.range d, rate d^(H+j.val+h)*|r (H+j.val+h)|) ≤
      Real.exp (-48)/(6*(d : ℝ)) :=
    (remaining_window_bound d (d-2) (H+j.val) hd (by omega) (by omega)).le
  have hb := weighted_window_bound_real d H w r
    (Real.exp (-48)/(6*(d : ℝ))) hr
  have hfirst := first_window_lower_real d H w hd
  have hgap : mass (weightedCoefficients d w)*(Real.exp (-48)/(6*(d : ℝ))) <
      Real.exp (-48)*mass (weightedCoefficients d w)/(rate d+1) := by
    rw [show mass (weightedCoefficients d w)*(Real.exp (-48)/(6*(d : ℝ))) =
      Real.exp (-48)*mass (weightedCoefficients d w)/(6*(d : ℝ)) by ring]
    apply div_lt_div_of_pos_left (by positivity) (by positivity)
    have hu := rate_upper_half d (by omega)
    have hh : (12 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  by_contra hnone
  push_neg at hnone
  have heq (h : ℕ) (hh : h ∈ Finset.range d) :
      (∑ j : ZMod d, w j*
        rawApply (List.range' 2 (d-2)) (geometricRowTail d) (H+h+j.val)) =
      -(∑ j : ZMod d, w j*r (H+h+j.val)) := by
    have hz := hnone (H+h) (by omega)
      (by have := Finset.mem_range.mp hh; omega)
    have hsplit : (∑ j : ZMod d, w j*rawTail (d-2) (H+h+j.val)) =
        (∑ j : ZMod d, w j*
          rawApply (List.range' 2 (d-2)) (geometricRowTail d) (H+h+j.val)) +
        ∑ j : ZMod d, w j*r (H+h+j.val) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [rawTail_split]
      have hidx : d-2+2=d := by omega
      have he (k : ℕ) : k+(d-2)+3=k+d+1 := by omega
      simp only [hidx, he, r, mul_add]
    rw [hsplit] at hz
    linarith
  have he : (∑ h ∈ Finset.range d, rate d^(H+h)*
      |∑ j : ZMod d, w j*
        rawApply (List.range' 2 (d-2)) (geometricRowTail d) (H+h+j.val)|) =
      ∑ h ∈ Finset.range d, rate d^(H+h)*
        |∑ j : ZMod d, w j*r (H+h+j.val)| := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [heq h hh, abs_neg]
  rw [he] at hfirst
  exact (not_lt_of_ge hfirst) (hb.trans_lt hgap)

/-- Raw-error Hankel blocks are invertible after a linear starting threshold. -/
theorem rawHankel_isUnit_linear (H : ℕ) (hd : 12 ≤ d) (hH : 420*d ≤ H) :
    IsUnit (rawHankel d H) := by
  have hker (w : ZMod d → ℝ) (hw : (rawHankel d H).mulVec w = 0) : w = 0 := by
    by_contra hne
    obtain ⟨n, hn, hnu, hdetect⟩ := real_weight_detection d H w hd hH hne
    let i : ZMod d := (n-H : ℕ)
    have hval : i.val = n-H := ZMod.val_natCast_of_lt (by omega)
    have he := congrFun hw i
    simp only [Matrix.mulVec, dotProduct, rawHankel, Pi.zero_apply, hval] at he
    have hn' : H+(n-H)=n := by omega
    simp only [hn'] at he
    apply hdetect
    simpa only [mul_comm] using he
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  apply sub_eq_zero.mp
  apply hker
  rw [Matrix.mulVec_sub, huv, sub_self]

theorem rawHankel_det_ne_zero_linear (H : ℕ) (hd : 12 ≤ d) (hH : 420*d ≤ H) :
    (rawHankel d H).det ≠ 0 := by
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det (rawHankel d H)).mp
    (rawHankel_isUnit_linear d H hd hH))

end
end LambertLinearHankel

#print axioms LambertLinearHankel.real_weight_detection
#print axioms LambertLinearHankel.rawHankel_isUnit_linear
#print axioms LambertLinearHankel.rawHankel_det_ne_zero_linear
