import Submission.ExceptionSieveDecision
import Submission.Staircase16

/-! The certified bound-sixteen moat yields a concrete rejecting cutoff in
the exact Boolean formulation. This verifies only C ≤ 16, not all C. -/
namespace Erdos952Investigation
namespace ExceptionSieveSixteen
open ExceptionSieveReduction ExceptionSieveDecision SieveQuantifiers
set_option maxHeartbeats 0

lemma inside_norm_bound {z : GaussianInt} (hz : Staircase16.Inside z) :
    z.norm ≤ 2*(6438 : ℤ)^2 := by
  obtain ⟨hr0,hr1,hi0,hi1⟩ := Staircase16.inside_coordinate_bound hz
  change -6438 ≤ z.re at hr0
  change z.re ≤ 6438 at hr1
  change -6438 ≤ z.im at hi0
  change z.im ≤ 6438 at hi1
  have hr : z.re^2 ≤ (6438 : ℤ)^2 := sq_le_sq.mpr (by
    rw [abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 6438)]
    exact abs_le.mpr ⟨hr0,hr1⟩)
  have hi : z.im^2 ≤ (6438 : ℤ)^2 := sq_le_sq.mpr (by
    rw [abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 6438)]
    exact abs_le.mpr ⟨hi0,hi1⟩)
  rw [gaussian_norm_sq]
  omega

lemma candidate_inside_closed (C : ℤ) (hC : C ≤ 16) {z w : GaussianInt}
    (hz : Staircase16.Inside z) (hw : (candidateGraph C 12877).Adj z w) :
    Staircase16.Inside w := by
  have hzB := inside_norm_bound hz
  have hnorm := norm_le_twice_norm_sub_add z w
  have hs := hw.2.2.2
  have hzN : z.norm ≤ (12877 : ℤ)^2 := by omega
  have hwN : w.norm ≤ (12877 : ℤ)^2 := by omega
  exact Staircase16.inside_closed Staircase16.all_rows_checked hz
    ((candidate_iff_prime_of_norm_le hzN).mp hw.1)
    ((candidate_iff_prime_of_norm_le hwN).mp hw.2.1) (hs.trans_le hC)

theorem cutoff_component_finite (C : ℤ) (hC : C ≤ 16) :
    {w | (candidateGraph C 12877).Reachable (3 : GaussianInt) w}.Finite := by
  apply Staircase16.inside_finite.subset
  have hwalk : ∀ {z w : GaussianInt}, (candidateGraph C 12877).Walk z w →
      Staircase16.Inside z → Staircase16.Inside w := by
    intro z w p
    induction p with
    | nil => exact id
    | cons h p ih => exact fun hz => ih (candidate_inside_closed C hC hz h)
  intro w hw
  exact hw.elim fun p => hwalk p Staircase16.three_inside

/-- An explicit rejecting cutoff, certified without evaluating the enormous
finite enumeration that defines cutoffTest. -/
theorem cutoffTest_false_le_sixteen (C : ℤ) (hC : C ≤ 16) :
    cutoffTest C 12877 = false :=
  (cutoffTest_false_iff C 12877).mpr (cutoff_component_finite C hC)

#print axioms cutoffTest_false_le_sixteen
end ExceptionSieveSixteen
end Erdos952Investigation
