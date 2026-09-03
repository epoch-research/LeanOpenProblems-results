import Submission.RationalBandFourierScales
import Submission.ResidueFourFactorReduction

/-! Finiteness forces a negative contribution outside any fixed finite
collection of rational-frequency bands, at one actual common scale. -/
namespace Erdos972RationalBandFourierObstruction

open Filter Finset ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972FloorCovarianceFourier Erdos972RationalBandFourierScales
open Erdos972DivisorMeanRecenter Erdos972ResidueCommonScales
open Erdos972GrowingTypeIIReduction Erdos972CenteredRowScales Erdos972Topology
open Erdos972FullRecenterCovarianceScales Erdos972CommonCovarianceScales
open Erdos972ResidueFourFactorReduction

set_option maxHeartbeats 2000000

theorem finite_primeSet_forces_negative_major_band_complement {α : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hfin : (primeSet α).Finite)
    (S : Finset ℤ) (T : Finset RationalMode) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < growingCutoff u ∧ 0 < scaleCutoff α u ∧
      OutputPrimeScale α u ∧ FullTwoSidedScale α u ∧ ResidueTwoSidedScale α u ∧
      |frequencyCovariance α (scaleCutoff α u)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (majorBands (floorMul α (scaleCutoff α u)+1) S T)ᶜ /
          (scaleCutoff α u : ℝ)+1| ≤ ε := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (eventually_major_bands_small hα.le S T (show 0 < ε/2 by positivity))
  obtain ⟨u, N, hu, rfl, hcut, hN, hrows, hfullrows, hresrows, hfull⟩ :=
    finite_primeSet_forces_negative_recentered_fourFactor_residues hα hI hfin
      (show 0 < ε/2 by positivity) (max B K)
  have hlow := hK u ((le_max_right B K).trans hu.le) hresrows
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr hN
  let R := fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n
  let A := majorBands (floorMul α (scaleCutoff α u)+1) S T
  have hs := recentered_fourFactor_frequency_split hα.le (scaleCutoff α u)
    (growingCutoff u) (growingCutoff u) (growingCutoff u) (growingCutoff u) A
  have hl : |frequencyCovariance α (scaleCutoff α u) R R A/(scaleCutoff α u : ℝ)| ≤ ε/2 := by
    rw [abs_div, abs_of_pos hNR]
    exact (div_le_iff₀ hNR).mpr hlow
  refine ⟨u, (le_max_left B K).trans_lt hu, (le_max_left B K).trans_lt hcut,
    hN, hrows, hfullrows, hresrows, ?_⟩
  have he : frequencyCovariance α (scaleCutoff α u) R R Aᶜ/(scaleCutoff α u : ℝ)+1 =
      (meanCenteredFourFactor α (scaleCutoff α u) (growingCutoff u) (growingCutoff u)
        (growingCutoff u) (growingCutoff u)/(scaleCutoff α u : ℝ)+1)-
      frequencyCovariance α (scaleCutoff α u) R R A/(scaleCutoff α u : ℝ) := by
    rw [hs]
    ring
  change |frequencyCovariance α (scaleCutoff α u) R R Aᶜ/(scaleCutoff α u : ℝ)+1| ≤ ε
  rw [he]
  exact (abs_sub _ _).trans (by linarith only [hfull, hl])


#print axioms finite_primeSet_forces_negative_major_band_complement
end Erdos972RationalBandFourierObstruction
