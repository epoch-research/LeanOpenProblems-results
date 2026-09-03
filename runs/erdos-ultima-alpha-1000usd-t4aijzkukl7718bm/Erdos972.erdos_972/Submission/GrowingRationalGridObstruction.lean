import Submission.GrowingRationalGridBudgets
import Submission.ResidueFourFactorReduction

/-! A growing rational-grid estimate and its exact finiteness obstruction.
No bound for the signed contribution on the complementary frequencies is asserted. -/
namespace Erdos972GrowingRationalGridObstruction

open Filter Finset ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972FloorCovarianceFourier Erdos972GrowingRationalGrid
open Erdos972GrowingRationalGridBudgets Erdos972ResidueCommonScales
open Erdos972ResidueFourFactorReduction Erdos972DivisorMeanRecenter
open Erdos972GrowingTypeIIReduction Erdos972CenteredRowScales
open Erdos972CovarianceScaleBudgets Erdos972PolynomialRowScales Erdos972GrowingTypeI
open Erdos972RecenteredPrefixScales Erdos972ScaledPrimeRows Erdos972DualPrimeRows
open Erdos972ResiduePrimeRows Erdos972ResidueDivisorCounts
open Erdos972TwoBandFourierObstruction Erdos972LowFloorFourierScales
open Erdos972FullRecenterCovarianceScales Erdos972CommonCovarianceScales Erdos972Topology

set_option maxHeartbeats 2000000
attribute [local irreducible] root64

/-- This estimate is uniform on an explicitly growing set. It is derived
from the finite bound and its quantitative budget, not from fixed-mode limits. -/
theorem eventually_rationalGrid_norm_sum_small {α : ℝ} (hα : 1 ≤ α)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, ResidueTwoSidedScale α u →
      (∑ k ∈ rationalGrid (floorMul α (scaleCutoff α u)+1) (bandCutoff u),
        ‖covarianceFourierTerm α (scaleCutoff α u)
          (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
          (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n) k /
            ((floorMul α (scaleCutoff α u)+1 : ℕ) : ℂ)‖) ≤ ε*(scaleCutoff α u : ℝ) := by
  filter_upwards [eventually_gridBudget_small hα hε, eventually_reciprocal_cutoff_le_one,
    growingCutoff_tendsto.eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊]
    with u hbudget hm hW hu huα
  intro hrows
  let N := scaleCutoff α u
  let v := root64 u
  let W := growingCutoff u
  let Q := bandCutoff u
  let L := 1+Real.log (α*N)
  let Ep := scaledRowError (dualScaleLoss α) u v
  let Bd := 236*(v : ℝ)*(u : ℝ)^4
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  obtain ⟨huN, hNu, _⟩ := scaleCutoff_bounds hα hu hαu
  have hN : 0 < N := hu.trans huN
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hvN : v ≤ N := (root64_le u).trans huN
  have hL : 1 ≤ L := (scale_log_bound hα hu hαu).1
  have hlog : Real.log N ≤ L-1 := by
    have hh := Real.log_le_log hNR (le_mul_of_one_le_left hNR.le hα)
    dsimp only [L]
    linarith only [hh]
  have hlogM : Real.log (floorMul α N) ≤ L-1 := by
    have hh := log_floorMul_le hα (mem_Ioc.mpr ⟨hN, le_rfl⟩)
    dsimp only [L]
    linarith only [hh]
  have hBd : 0 ≤ Bd := by dsimp only [Bd]; positivity
  obtain ⟨hQ, _, hQv⟩ := bandCutoff_bounds hu
  have hp : ∀ q ∈ Ioc 0 Q, ∀ X ≤ N, ∀ j < q,
      |inputResidueRow α q j X-Chebyshev.psi X/q| ≤ Ep := by
    intro q hq X hX j hj
    exact hrows.1 q (mem_Ioc.mp hq).1 ((mem_Ioc.mp hq).2.trans hQv) j hj X (hX.trans hNu)
  have hd : ∀ q ∈ Ioc 0 Q, ∀ X ≤ N, ∀ d ∈ Ioc 0 v, ∀ j < q,
      |((residueDivisorPairs α X d q j).card : ℝ)-(X : ℝ)/(d*q)| ≤ Bd := by
    intro q hq X hX d hd j hj
    exact hrows.2 d q (mem_Ioc.mp hd).1 (mem_Ioc.mp hq).1 ((mem_Ioc.mp hq).2.trans hQv) j hj X hX
  have hh := rationalGrid_norm_sum_bound hα hW (growingCutoff_eligible u).2 hvN hQ
    hL hlog hlogM hm hBd hp hd
  exact hh.trans hbudget

noncomputable def gridWithLow (J : ℕ) [NeZero J] (B : ℕ) (S : Finset ℤ) : Finset (ZMod J) :=
  rationalGrid J B ∪ S.image (fun k : ℤ => (k : ZMod J))

/-- Any fixed finite low-frequency set may be added on the SAME scales. -/
theorem eventually_gridWithLow_small {α : ℝ} (hα : 1 ≤ α) (S : Finset ℤ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, ResidueTwoSidedScale α u →
      |frequencyCovariance α (scaleCutoff α u)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (gridWithLow (floorMul α (scaleCutoff α u)+1) (bandCutoff u) S)| ≤
          ε*(scaleCutoff α u : ℝ) := by
  have hδ : 0 < ε/(2*(S.card+1)) := by positivity
  have hs := (eventually_all_finset S).mpr (fun k hk => eventually_fourier_term_small hα k hδ)
  filter_upwards [hs, eventually_rationalGrid_norm_sum_small hα (show 0 < ε/2 by positivity)]
    with u huS huG
  intro hrows
  let N := scaleCutoff α u
  let J := floorMul α N+1
  let R := fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n
  let F := fun k : ZMod J => covarianceFourierTerm α N R R k/(J : ℂ)
  have hJ : (0 : ℝ) < J := by dsimp only [J]; positivity
  have hS : (∑ k ∈ S.image (fun k : ℤ => (k : ZMod J)), ‖F k‖) ≤ ε/2*(N : ℝ) := by
    apply image_norm_sum_bound S _ F (by positivity)
    intro k hk
    dsimp only [F]
    rw [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hJ).mpr
    have hh := huS k hk
    change ‖covarianceFourierTerm α N R R (k : ZMod J)‖ ≤ ε/(2*(S.card+1))*(J : ℝ)*(N : ℝ) at hh
    exact hh.trans_eq (by rw [div_mul_eq_div_div]; ring)
  have hG := huG hrows
  have hh := union_norm_sum_bound _ _ F hG hS
  change |frequencyCovariance α N R R (gridWithLow J (bandCutoff u) S)| ≤ ε*(N : ℝ)
  unfold frequencyCovariance
  rw [sum_div]
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_sum_le _ _).trans
  change (∑ k ∈ gridWithLow J (bandCutoff u) S, ‖F k‖) ≤ _
  dsimp only [gridWithLow]
  linarith only [hh]

/-- Finiteness forces a near -N contribution outside the explicit growing
grid, with all original, dual and residue rows retained at that same scale. -/
theorem finite_primeSet_forces_negative_growing_grid_complement {α : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hfin : (primeSet α).Finite)
    (S : Finset ℤ) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < growingCutoff u ∧ B < bandCutoff u ∧ 0 < scaleCutoff α u ∧
      OutputPrimeScale α u ∧ FullTwoSidedScale α u ∧ ResidueTwoSidedScale α u ∧
      |frequencyCovariance α (scaleCutoff α u)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (gridWithLow (floorMul α (scaleCutoff α u)+1) (bandCutoff u) S)ᶜ /
          (scaleCutoff α u : ℝ)+1| ≤ ε := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    ((eventually_gridWithLow_small hα.le S (show 0 < ε/2 by positivity)).and
      (bandCutoff_tendsto.eventually_gt_atTop B))
  obtain ⟨u, N, hu, rfl, hcut, hN, hrows, hfullrows, hresrows, hfull⟩ :=
    finite_primeSet_forces_negative_recentered_fourFactor_residues hα hI hfin
      (show 0 < ε/2 by positivity) (max B K)
  obtain ⟨hlow', hband⟩ := hK u ((le_max_right B K).trans hu.le)
  have hlow := hlow' hresrows
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr hN
  let R := fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n
  let A := gridWithLow (floorMul α (scaleCutoff α u)+1) (bandCutoff u) S
  have hs := recentered_fourFactor_frequency_split hα.le (scaleCutoff α u)
    (growingCutoff u) (growingCutoff u) (growingCutoff u) (growingCutoff u) A
  have hl : |frequencyCovariance α (scaleCutoff α u) R R A/(scaleCutoff α u : ℝ)| ≤ ε/2 := by
    rw [abs_div, abs_of_pos hNR]
    exact (div_le_iff₀ hNR).mpr hlow
  refine ⟨u, (le_max_left B K).trans_lt hu, (le_max_left B K).trans_lt hcut,
    hband, hN, hrows, hfullrows, hresrows, ?_⟩
  have he : frequencyCovariance α (scaleCutoff α u) R R Aᶜ/(scaleCutoff α u : ℝ)+1 =
      (meanCenteredFourFactor α (scaleCutoff α u) (growingCutoff u) (growingCutoff u)
        (growingCutoff u) (growingCutoff u)/(scaleCutoff α u : ℝ)+1)-
      frequencyCovariance α (scaleCutoff α u) R R A/(scaleCutoff α u : ℝ) := by
    rw [hs]
    ring
  change |frequencyCovariance α (scaleCutoff α u) R R Aᶜ/(scaleCutoff α u : ℝ)+1| ≤ ε
  rw [he]
  exact (abs_sub _ _).trans (by linarith only [hfull, hl])

#print axioms eventually_rationalGrid_norm_sum_small
#print axioms finite_primeSet_forces_negative_growing_grid_complement
end Erdos972GrowingRationalGridObstruction
