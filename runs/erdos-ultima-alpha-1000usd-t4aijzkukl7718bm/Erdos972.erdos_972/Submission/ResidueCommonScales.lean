import Submission.ResidueDivisorCounts
import Submission.FullRecenterCovarianceScales

/-! The original, dual, joint-divisor and every-residue rows are retained
from a single common rational scale. -/
namespace Erdos972ResidueCommonScales

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972RationalRotationCount Erdos972BeattyRows
open Erdos972WeightedPrimeRotation Erdos972ScaledPrimeRows Erdos972PolynomialRowScales
open Erdos972InverseGoodApproximation Erdos972ReciprocalDivisorCounts
open Erdos972DivisorPairCount Erdos972CenteredRowScales Erdos972PrimeRotation
open Erdos972DualPrimeRows Erdos972ResiduePrimeRows Erdos972ResidueDivisorCounts
open Erdos972FullRecenterCovarianceScales Erdos972GrowingTypeIIReduction Erdos972CommonCovarianceScales

set_option maxHeartbeats 2000000
attribute [local irreducible] root64

def ResidueTwoSidedScale (α : ℝ) (u : ℕ) : Prop :=
  (∀ e : ℕ, 0 < e → e ≤ root64 u → ∀ j < e, ∀ X : ℕ, X ≤ u^6 →
    |inputResidueRow α e j X-Chebyshev.psi X/e| ≤ scaledRowError (dualScaleLoss α) u (root64 u)) ∧
  (∀ d e : ℕ, 0 < d → 0 < e → e ≤ root64 u → ∀ j < e, ∀ X ≤ scaleCutoff α u,
    |((residueDivisorPairs α X d e j).card : ℝ)-(X : ℝ)/(d*e)| ≤ 236*(root64 u : ℝ)*(u : ℝ)^4)

theorem exists_all_residue_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 4*α ≤ u ∧ 2048*dualScaleLoss α ≤ root64 u ∧
      OutputPrimeScale α u ∧ FullTwoSidedScale α u ∧ ResidueTwoSidedScale α u := by
  let K := dualScaleLoss α
  have hK : 0 < K := dualScaleLoss_pos hα.le
  let C := max B (max (⌈4*α⌉₊+1) ((2048*K)^64))
  obtain ⟨u, v, r, hu, hv, hvu, huv, rfl, hr, hlo, hhi, hrows⟩ :=
    exists_polynomial_beatty_arc_scale_data hα hI C
  have hu0 : 0 < u := (Nat.zero_le C).trans_lt hu
  have hαu : 4*α ≤ u := (Nat.le_ceil _).trans (by
    exact_mod_cast (Nat.le_succ ⌈4*α⌉₊).trans
      ((le_max_left (⌈4*α⌉₊+1) ((2048*K)^64)).trans ((le_max_right B _).trans hu.le)))
  have hKu : (2048*K)^64 ≤ u :=
    (le_max_right (⌈4*α⌉₊+1) _).trans ((le_max_right B _).trans hu.le)
  have hKv : 2048*K ≤ root64 u := (le_root64_iff _ _).mpr hKu
  have hq : 2*α ≤ r.den := by
    have hu4 : (u : ℝ) ≤ (u : ℝ)^4 := by exact_mod_cast Nat.le_self_pow (by norm_num : 4 ≠ 0) u
    have hloR : (u : ℝ)^4 ≤ r.den := by exact_mod_cast hlo
    linarith only [hα, hαu, hu4, hloR]
  obtain ⟨s, hslo, hshi, hs⟩ := inverse_good_approximant hα.le r hr hq (Nat.le_ceil α)
  change r.den ≤ K*s.den at hslo
  change s.den ≤ K*r.den at hshi
  have hslo' : u^4 ≤ K*s.den := hlo.trans hslo
  have hshi' : s.den ≤ 16*K*u^4 := by
    have hh := hshi.trans (Nat.mul_le_mul_left K hhi)
    nlinarith only [hh]
  have hXscale (X : ℕ) (hX : X ≤ scaleCutoff α u) : α*X ≤ (u : ℝ)^6 := by
    have hα0 : 0 < α := by linarith
    have hh : (scaleCutoff α u : ℝ) ≤ (u : ℝ)^6/α := Nat.floor_le (by positivity)
    have hXR : (X : ℝ) ≤ scaleCutoff α u := Nat.cast_le.mpr hX
    have hh' := (le_div_iff₀ hα0).mp (hXR.trans hh)
    nlinarith only [hh']
  refine ⟨u, (le_max_left B _).trans_lt hu, hαu, hKv, hrows, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro e he hev X hX
    exact input_divisor_row_discrepancy (by linarith : 0 ≤ α) s hs hK hKv hvu hslo' hshi' he hev hX
  · intro d e hd he hev X hX
    exact reciprocal_scale_divisor_prefix_bound hα.le r hr hu0
      (show 0 < root64 u by omega) hαu hlo hhi (hXscale X hX) hd he hev
  · intro e he hev j hj X hX
    exact input_residue_row_discrepancy (by linarith : 0 ≤ α) s hs hK hKv hvu hslo' hshi' he hev hj hX
  · intro d e hd he hev j hj X hX
    exact reciprocal_scale_residue_prefix_bound hα.le r hr hu0
      (show 0 < root64 u by omega) hαu hlo hhi (hXscale X hX) hd he hev hj

#print axioms exists_all_residue_scale
end Erdos972ResidueCommonScales
