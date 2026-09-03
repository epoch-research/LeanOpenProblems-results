import Submission.MidpointFourierBounds
import Submission.FullRecenterCovarianceScales

/-! Midpoint Fourier modes are sublinear on the actual two-sided prime-row
scales. All eventual thresholds precede any selection of a good scale. -/
namespace Erdos972MidpointFourierScales

open Filter Finset ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972FloorCovarianceFourier Erdos972MidpointFourierBounds
open Erdos972DivisorMeanRecenter Erdos972FullRecenterCovarianceScales
open Erdos972GrowingTypeIIReduction Erdos972CenteredRowScales
open Erdos972CovarianceScaleBudgets Erdos972TypeICovarianceScales
open Erdos972PolynomialRowScales Erdos972DualPrimeRows Erdos972ScaledPrimeRows
open Erdos972RecenteredPrefixScales Erdos972GrowingTypeI

set_option maxHeartbeats 2000000
attribute [local irreducible] root64

/-- This conclusion concerns a frequency of size J/2, not a fixed integer
mode. Its smallness uses the dual prime-input and joint divisor rows. -/
theorem eventually_midpoint_term_small {α : ℝ} (hα : 1 ≤ α) (j : ℤ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, FullTwoSidedScale α u →
      ‖covarianceFourierTerm α (scaleCutoff α u)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (midpointFrequency (floorMul α (scaleCutoff α u)+1) j :
          ZMod (floorMul α (scaleCutoff α u)+1)) /
        ((floorMul α (scaleCutoff α u)+1 : ℕ) : ℂ)‖ ≤ ε*(scaleCutoff α u : ℝ) := by
  let C := 1+2*Real.pi*(|(j : ℝ)|+1)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hδ : 0 < ε/(5*C) := by positivity
  filter_upwards [eventually_dual_covariance_budget hα hδ,
    eventually_covariance_budget hα hδ,
    eventually_reciprocal_cutoff_le_one, growingCutoff_tendsto.eventually_ge_atTop 1,
    root64_tendsto.eventually_ge_atTop 2,
    eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊]
    with u hdual hbudget hm hW hv2 hu huα
  intro hrows
  let N := scaleCutoff α u
  let v := root64 u
  let W := growingCutoff u
  let L := 1+Real.log (α*N)
  let Ep := scaledRowError (dualScaleLoss α) u v
  let Bd := 118*(v : ℝ)*(u : ℝ)^4
  let D := 2*|covariance N (fun n => vonMangoldt n) (fun n => Real.log n)|+
    50*(v : ℝ)*L^3*(Ep+Bd+1)
  let E := 100*(Bd+1)*(v : ℝ)^2*L^5
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
  have hEp : 0 ≤ Ep := by
    dsimp only [Ep, scaledRowError, v]
    positivity [Erdos972PrimeRotation.rotationConstant_pos (256*dualScaleLoss α), Real.log_natCast_nonneg u]
  have hBd : 0 ≤ Bd := by dsimp only [Bd]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity [hL]
  have hprime : ∀ X ≤ N, |inputDivisorRow α 2 X-Chebyshev.psi X/2| ≤ Ep := by
    intro X hX
    simpa only [Nat.cast_ofNat] using hrows.1 2 (by norm_num) hv2 X (hX.trans hNu)
  have hdiv : ∀ X ≤ N, ∀ a ∈ Ioc 0 v, ∀ b ∈ Ioc 0 2,
      |((Erdos972DivisorPairCount.divisorPairs α X a b).card : ℝ)-(X : ℝ)/(a*b)| ≤ Bd := by
    intro X hX a ha b hb
    exact hrows.2 a b (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1 ((mem_Ioc.mp hb).2.trans hv2) X hX
  have hh := midpoint_fourier_term_bound hα hW (growingCutoff_eligible u).2 hvN hL hlog hlogM
    hm hBd hprime hdiv (midpointFrequency (floorMul α N+1) j) (midpointFrequency_near _ j)
  change ‖covarianceFourierTerm α N (fun n => meanCenteredTypeII W W n)
      (fun n => meanCenteredTypeII W W n)
      (midpointFrequency (floorMul α N+1) j : ZMod (floorMul α N+1)) /
        ((floorMul α N+1 : ℕ) : ℂ)‖ ≤ ε*(N : ℝ)
  change _ ≤ 5*C*(v : ℝ)*L^2*(2*Ep+64*(v : ℝ)*L^3*(Bd+1)) at hh
  have hminor : 10*(v : ℝ)*L^2*Ep ≤ D := by
    have hp := pow_le_pow_right₀ hL (show 2 ≤ 3 by norm_num)
    have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ 10*(v : ℝ)*Ep by positivity)
    have hz : 0 ≤ (v : ℝ)*L^3*Ep := by positivity [hL]
    have hz' : 0 ≤ (v : ℝ)*L^3*(Bd+1) := by positivity [hL]
    have hc := abs_nonneg (covariance N (fun n => vonMangoldt n) (fun n => Real.log n))
    dsimp only [D]
    nlinarith only [hmul, hz, hz', hc]
  have hcompare : 5*C*(v : ℝ)*L^2*(2*Ep+64*(v : ℝ)*L^3*(Bd+1)) ≤ C*(D+4*E) := by
    have hm := mul_le_mul_of_nonneg_left hminor hC.le
    have he := mul_nonneg hC.le hE
    dsimp only [E] at he ⊢
    nlinarith only [hm, he]
  change D ≤ ε/(5*C)*(N : ℝ) at hdual
  change E ≤ ε/(5*C)*(N : ℝ) at hbudget
  have he := mul_le_mul_of_nonneg_left (add_le_add hdual
    (mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : ℝ) ≤ 4))) hC.le
  have heq : C*(ε/(5*C)*(N : ℝ)+4*(ε/(5*C)*(N : ℝ))) = ε*(N : ℝ) := by field_simp; ring
  rw [heq] at he
  exact hh.trans (hcompare.trans he)

/-- A fixed finite band around J/2 is small on these same actual row scales.
Possible collisions of the residue image are included in the estimate. -/
theorem eventually_midpoint_band_small {α : ℝ} (hα : 1 ≤ α)
    (S : Finset ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, FullTwoSidedScale α u →
      |frequencyCovariance α (scaleCutoff α u)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (S.image (fun j : ℤ => (midpointFrequency (floorMul α (scaleCutoff α u)+1) j :
          ZMod (floorMul α (scaleCutoff α u)+1))))| ≤ ε*(scaleCutoff α u : ℝ) := by
  have hδ : 0 < ε/(S.card+1) := by positivity
  have hevent := (eventually_all_finset S).mpr
    (fun j hj => eventually_midpoint_term_small hα j hδ)
  filter_upwards [hevent] with u hu
  intro hrows
  let N := scaleCutoff α u
  let J := floorMul α N+1
  let R := fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n
  let K := S.image (fun j : ℤ => (midpointFrequency J j : ZMod J))
  have hsum : ‖∑ k ∈ K, covarianceFourierTerm α N R R k/(J : ℂ)‖ ≤
      (S.card : ℝ)*(ε/(S.card+1)*(N : ℝ)) := by
    apply (norm_sum_le _ _).trans
    apply (sum_image_le_of_nonneg (fun k hk => norm_nonneg (covarianceFourierTerm α N R R k/(J : ℂ)))).trans
    exact (sum_le_sum (fun j hj => hu j hj hrows)).trans_eq (by simp only [sum_const, nsmul_eq_mul]; rfl)
  have hcard : (S.card : ℝ)/(S.card+1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  have hh := mul_le_mul_of_nonneg_right hcard (show 0 ≤ ε*(N : ℝ) by positivity)
  have heq : (S.card : ℝ)*(ε/(S.card+1)*(N : ℝ)) =
      (S.card : ℝ)/(S.card+1)*(ε*(N : ℝ)) := by ring
  rw [heq] at hsum
  change |frequencyCovariance α N R R K| ≤ ε*(N : ℝ)
  unfold frequencyCovariance
  rw [sum_div]
  exact (Complex.abs_re_le_norm _).trans (by linarith only [hsum, hh])

#print axioms eventually_midpoint_term_small
#print axioms eventually_midpoint_band_small

end Erdos972MidpointFourierScales
