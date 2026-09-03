import Submission.UnitOrbitArithmetic
import Submission.UnitOrbitPhaseDescent
import Submission.UnitOrbitPhaseProbability

/-! Arithmetic phase-sensitive necessary collision budget. It remains
conditional on period minimality and does not establish an upper bound. -/
namespace Erdos7UnitOrbitPhaseArithmetic
open Erdos7Reduction Erdos7UnitOrbitDescent Erdos7UnitOrbitArithmetic
open Erdos7UnitOrbitPhaseDescent
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

variable {I : Type} [Fintype I]

/-- An actual arithmetic necessary condition, with harmless same-phase
copies removed from the pair count. -/
theorem minimal_period_phase_collision_budget [LinearOrder I]
    (N : ℕ) [NeZero N] (hN : 1 < N)
    (m : I → ℕ) (a : I → ℤ) (hd : ∀ i, m i ∣ N)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i)
    (hmin : ∀ D, D < N → ¬ HasOddArithmeticCover D (Fintype.card I))
    (u : (ZMod N)ˣ) (hu : Odd (orderOf u)) :
    let J := UnitIndex m a
    let H (i : J) := (ZMod (m i.val))ˣ
    let π (i : J) := unitMap N m hd i.val
    N.totient ≤
      (∑ i : J, ((Finset.univ : Finset (ZMod N)ˣ).filter (fun v =>
        Active H π (unitResidue m a) u v i ∧ orderOf (π i u) = 1)).card) +
      (∑ ij : PairIndex (I := J), ((Finset.univ : Finset (ZMod N)ˣ).filter (fun v =>
        Active H π (unitResidue m a) u v ij.val.1 ∧
        Active H π (unitResidue m a) u v ij.val.2 ∧
        orderOf (π ij.val.1 u) = orderOf (π ij.val.2 u) ∧
        orderOf (π ij.val.1 u) ≠ 1 ∧
        ¬ CoActive H π (unitResidue m a) u v ij.val.1 ij.val.2)).card) := by
  dsimp only
  have hh := phase_collision_count_bound _ _ _ (unit_cover N m a hd hc) u hu
    (no_smaller_unit_cover N hN m a hmin u)
  simpa only [ZMod.card_units_eq_totient] using hh

#print axioms minimal_period_phase_collision_budget
end
end Erdos7UnitOrbitPhaseArithmetic
