import Submission.LocalRationalHoleScales
import Submission.NarrowPrimePairMoment

/-! Finiteness forces a cubic lower-tail moment even after deleting the
actual rational exceptional sets, at arbitrarily large common metric scales. -/
namespace Erdos972RationalExcludedDeficit

open Set MeasureTheory Filter
open Erdos972Topology Erdos972NarrowPrimePairMoment
open Erdos972WideMetricSieve Erdos972LocalRationalHoleScales

/-- The half-hole hypothesis of the earlier moment obstruction is now
proved for the actual excluded sets. This remains an obstruction, not an
upper estimate for the moment. -/
theorem finite_primeSet_forces_excluded_deficit {α a b : ℝ} (A : ℕ)
    (hα : 1 < α) (hI : Irrational α) (ha : a < α) (hb : α < b)
    (hfin : (primeSet α).Finite) :
    ∃ B : ℕ, ∀ V : ℕ, ∃ v : ℕ, V < v ∧ 2 ≤ v ∧ A ≤ v ∧
      ((v^40 : ℕ) : ℝ)^3 / 262144 ≤
        deficitMoment A B (v^40) a b (wideBadSlopes A (v^24) (v^28)) := by
  obtain ⟨B, hB⟩ := finite_primeSet_forces_deficit_moment A ha hb hfin
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hB
  refine ⟨B, fun V => ?_⟩
  obtain ⟨v, hv, hv2, hloss⟩ := exists_half_hole_scale hα hI A (max V (max N₀ A))
  have hVv : V < v := (le_max_left _ _).trans_lt hv
  have hNv : N₀ ≤ v := ((le_max_left N₀ A).trans (le_max_right V _)).trans hv.le
  have hAv : A ≤ v := ((le_max_right N₀ A).trans (le_max_right V _)).trans hv.le
  have hvpow : v ≤ v^40 := by
    simpa using Nat.pow_le_pow_right (show 0 < v by omega) (show 1 ≤ 40 by omega)
  have hh := (hN₀ (v^40) (hNv.trans hvpow)).2
    (wideBadSlopes A (v^24) (v^28)) (measurableSet_wideBadSlopes _ _ _) hloss
  exact ⟨v, hVv, hv2, hAv, hh⟩

#print axioms finite_primeSet_forces_excluded_deficit
end Erdos972RationalExcludedDeficit
