import Submission.LowFloorFourierScales

/-! A finite prime-pair set forces a negative contribution outside EVERY
fixed finite set of Fourier frequencies, at actual common good scales. -/
namespace Erdos972HighFloorFourierObstruction

open Filter Finset ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972FloorCovarianceFourier Erdos972LowFloorFourierScales
open Erdos972DivisorMeanRecenter Erdos972RecenterFourFactorReduction
open Erdos972GrowingTypeIIReduction Erdos972CenteredRowScales
open Erdos972Topology Erdos972CommonCovarianceScales

set_option maxHeartbeats 1500000

/-- The Fourier complement is taken in the full varying finite modulus.
No equality with the previously defined low-frequency Mellin integral is
assumed. Every centering term is included in the Fourier summand. -/
theorem finite_primeSet_forces_negative_high_frequencies {α : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hfin : (primeSet α).Finite)
    (S : Finset ℤ) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < growingCutoff u ∧ 0 < scaleCutoff α u ∧
      OutputPrimeScale α u ∧
      |frequencyCovariance α (scaleCutoff α u)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (S.image (fun k : ℤ => (k : ZMod (floorMul α (scaleCutoff α u)+1))))ᶜ /
          (scaleCutoff α u : ℝ)+1| ≤ ε := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_low_frequency_covariance_small hα.le S (show 0 < ε/2 by positivity))
  obtain ⟨u, N, hu, rfl, hcut, hN, hrows, hfull⟩ :=
    finite_primeSet_forces_negative_recentered_fourFactor hα hI hfin
      (show 0 < ε/2 by positivity) (max B T)
  have hlow := hT u ((le_max_right B T).trans hu.le)
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr hN
  let R := fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n
  let K := S.image (fun k : ℤ => (k : ZMod (floorMul α (scaleCutoff α u)+1)))
  have hs := recentered_fourFactor_frequency_split hα.le (scaleCutoff α u)
    (growingCutoff u) (growingCutoff u) (growingCutoff u) (growingCutoff u) K
  have hl : |frequencyCovariance α (scaleCutoff α u) R R K/(scaleCutoff α u : ℝ)| ≤ ε/2 := by
    rw [abs_div, abs_of_pos hNR]
    exact (div_le_iff₀ hNR).mpr hlow
  refine ⟨u, (le_max_left B T).trans_lt hu, (le_max_left B T).trans_lt hcut, hN, hrows, ?_⟩
  have he : frequencyCovariance α (scaleCutoff α u) R R Kᶜ/(scaleCutoff α u : ℝ)+1 =
      (meanCenteredFourFactor α (scaleCutoff α u) (growingCutoff u) (growingCutoff u)
        (growingCutoff u) (growingCutoff u)/(scaleCutoff α u : ℝ)+1)-
      frequencyCovariance α (scaleCutoff α u) R R K/(scaleCutoff α u : ℝ) := by
    rw [hs]
    ring
  change |frequencyCovariance α (scaleCutoff α u) R R Kᶜ/(scaleCutoff α u : ℝ)+1| ≤ ε
  rw [he]
  exact (abs_sub _ _).trans (by linarith only [hfull, hl])

#print axioms finite_primeSet_forces_negative_high_frequencies

end Erdos972HighFloorFourierObstruction
