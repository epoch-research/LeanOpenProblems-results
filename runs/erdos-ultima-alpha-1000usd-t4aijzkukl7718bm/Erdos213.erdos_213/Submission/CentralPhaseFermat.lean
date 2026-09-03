import Submission.CentralPhaseDoubling
import Submission.FermatArea

/-! The square-area theorem closes the arithmetic gap in the restricted
phase-doubling exclusion. This does not constrain arbitrary rotations or
arbitrary rational-distance configurations. -/
namespace Erdos213.CentralPhaseDoubling

lemma fourth_add_four_not_square {L : ℚ} (hL : L ≠ 0) :
    ¬ IsSquare (L^4+4) := by
  rintro ⟨w, hw⟩
  have hpos : 0 < L^2 := sq_pos_of_ne_zero hL
  have hw0 : w ≠ 0 := by
    intro hz
    rw [hz] at hw
    nlinarith only [hw, sq_nonneg (L^2)]
  apply FermatArea.no_rational_square_area (x := L^2) (y := 2) (z := |w|)
    hpos (by norm_num) (abs_pos.mpr hw0)
    (show (L^2)^2+(2 : ℚ)^2=|w|^2 by
      rw [sq_abs]
      linear_combination hw)
  convert IsSquare.sq L using 1
  ring

/-- Unconditional exclusion of the single phase-doubling matching rule,
not an exclusion of all possible representations of the missing lengths. -/
theorem phase_doubling_excluded {r u v L a : ℚ}
    (hr : r≠0) (hr1 : r^2≠1) (ha : a≠0) (haL : a^2=L^2-1)
    (hsum : u^2+v^2=r^2+1) (hdiff : v^2-u^2=L*(r^2-1)) :
    phaseReal r u v^2≠1+(2/L^2-1)*(r^2-1) := by
  have hL : L≠0 := by
    intro hz
    rw [hz] at haL
    nlinarith only [haL, sq_nonneg a]
  exact phase_doubling_excluded_of_quartic_obstruction hr hr1 ha haL hsum hdiff
    (fourth_add_four_not_square hL)

#print axioms fourth_add_four_not_square
#print axioms phase_doubling_excluded
end Erdos213.CentralPhaseDoubling
