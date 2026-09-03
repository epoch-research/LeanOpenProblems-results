import Submission.RationalBandFourierBounds
import Submission.ResidueRecenterScales
import Submission.TwoBandFourierObstruction

/-! General rational-frequency bands at the same actual common row scales. -/
namespace Erdos972RationalBandFourierScales

open Filter Finset ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972FloorCovarianceFourier Erdos972RationalBandFourierBounds
open Erdos972DivisorMeanRecenter Erdos972ResidueCommonScales
open Erdos972GrowingTypeIIReduction Erdos972CenteredRowScales
open Erdos972CovarianceScaleBudgets Erdos972TypeICovarianceScales
open Erdos972PolynomialRowScales Erdos972DualPrimeRows Erdos972ScaledPrimeRows
open Erdos972RecenteredPrefixScales Erdos972GrowingTypeI
open Erdos972ResiduePrimeRows Erdos972ResidueDivisorCounts
open Erdos972TwoBandFourierObstruction Erdos972LowFloorFourierScales

set_option maxHeartbeats 2000000
attribute [local irreducible] root64

theorem eventually_rational_term_small {α : ℝ} (hα : 1 ≤ α) {q : ℕ} (hq : 0 < q)
    (a j : ℤ) (ha : (a : ZMod q) ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, ResidueTwoSidedScale α u →
      ‖covarianceFourierTerm α (scaleCutoff α u)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (rationalFrequency (floorMul α (scaleCutoff α u)+1) q a j :
          ZMod (floorMul α (scaleCutoff α u)+1)) /
        ((floorMul α (scaleCutoff α u)+1 : ℕ) : ℂ)‖ ≤ ε*(scaleCutoff α u : ℝ) := by
  let C := (1+2*Real.pi*(|(j : ℝ)|+1))*(q : ℝ)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hδ : 0 < ε/(5*C) := by positivity
  filter_upwards [eventually_dual_covariance_budget hα hδ,
    eventually_covariance_budget hα hδ,
    eventually_reciprocal_cutoff_le_one, growingCutoff_tendsto.eventually_ge_atTop 1,
    root64_tendsto.eventually_ge_atTop q,
    eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊]
    with u hdual hbudget hm hW hqv hu huα
  intro hrows
  let N := scaleCutoff α u
  let v := root64 u
  let W := growingCutoff u
  let L := 1+Real.log (α*N)
  let Ep := scaledRowError (dualScaleLoss α) u v
  let B := 118*(v : ℝ)*(u : ℝ)^4
  let D := 2*|covariance N (fun n => vonMangoldt n) (fun n => Real.log n)|+
    50*(v : ℝ)*L^3*(Ep+B+1)
  let E := 100*(B+1)*(v : ℝ)^2*L^5
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
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity [hL]
  have hprime : ∀ X ≤ N, ∀ r < q, |inputResidueRow α q r X-Chebyshev.psi X/q| ≤ Ep := by
    intro X hX r hr
    exact hrows.1 q hq hqv r hr X (hX.trans hNu)
  have hdiv : ∀ X ≤ N, ∀ d ∈ Ioc 0 v, ∀ r < q,
      |((residueDivisorPairs α X d q r).card : ℝ)-(X : ℝ)/(d*q)| ≤ 2*B := by
    intro X hX d hd r hr
    exact (hrows.2 d q (mem_Ioc.mp hd).1 hq hqv r hr X hX).trans_eq (by dsimp only [B, v]; ring)
  have hh := rational_fourier_term_bound hα hW (growingCutoff_eligible u).2 hvN hq a ha
    hL hlog hlogM hm (show 0 ≤ 2*B by positivity) hprime hdiv
    (rationalFrequency (floorMul α N+1) q a j) (rationalFrequency_near _ _ _ _)
  change ‖covarianceFourierTerm α N (fun n => meanCenteredTypeII W W n)
      (fun n => meanCenteredTypeII W W n)
      (rationalFrequency (floorMul α N+1) q a j : ZMod (floorMul α N+1)) /
        ((floorMul α N+1 : ℕ) : ℂ)‖ ≤ ε*(N : ℝ)
  have hh' : ‖covarianceFourierTerm α N (fun n => meanCenteredTypeII W W n)
      (fun n => meanCenteredTypeII W W n)
      (rationalFrequency (floorMul α N+1) q a j : ZMod (floorMul α N+1)) /
        ((floorMul α N+1 : ℕ) : ℂ)‖ ≤
          5*C*(v : ℝ)*L^2*(Ep+40*(v : ℝ)*L^2*(2*B+1)) := by
    exact hh.trans_eq (by dsimp only [C]; ring)
  have hminor : 5*(v : ℝ)*L^2*Ep ≤ D := by
    have hp := pow_le_pow_right₀ hL (show 2 ≤ 3 by norm_num)
    have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ 5*(v : ℝ)*Ep by positivity)
    have hz : 0 ≤ (v : ℝ)*L^3*Ep := by positivity [hL]
    have hz' : 0 ≤ (v : ℝ)*L^3*(B+1) := by positivity [hL]
    have hc := abs_nonneg (covariance N (fun n => vonMangoldt n) (fun n => Real.log n))
    dsimp only [D]
    nlinarith only [hmul, hz, hz', hc]
  have hlarge : 200*(v : ℝ)^2*L^4*(2*B+1) ≤ 4*E := by
    calc
      _ ≤ 200*(v : ℝ)^2*L^5*(2*(B+1)) := by
        have hp := pow_le_pow_right₀ hL (show 4 ≤ 5 by norm_num)
        have hc : 2*B+1 ≤ 2*(B+1) := by linarith
        have hm' := mul_le_mul hp hc (show 0 ≤ 2*B+1 by positivity)
          (show 0 ≤ L^5 by positivity [hL])
        nlinarith only [mul_le_mul_of_nonneg_left hm' (show 0 ≤ 200*(v : ℝ)^2 by positivity)]
      _ = _ := by dsimp only [E]; ring
  have hcompare : 5*C*(v : ℝ)*L^2*(Ep+40*(v : ℝ)*L^2*(2*B+1)) ≤ C*(D+4*E) := by
    have hm' := mul_le_mul_of_nonneg_left hminor hC.le
    have hl' := mul_le_mul_of_nonneg_left hlarge hC.le
    nlinarith only [hm', hl']
  change D ≤ ε/(5*C)*(N : ℝ) at hdual
  change E ≤ ε/(5*C)*(N : ℝ) at hbudget
  have he' := mul_le_mul_of_nonneg_left (add_le_add hdual
    (mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : ℝ) ≤ 4))) hC.le
  have heq : C*(ε/(5*C)*(N : ℝ)+4*(ε/(5*C)*(N : ℝ))) = ε*(N : ℝ) := by field_simp; ring
  rw [heq] at he'
  exact hh'.trans (hcompare.trans he')

structure RationalMode where
  den : ℕ
  num : ℤ
  offset : ℤ
  den_pos : 0 < den
  nonzero : (num : ZMod den) ≠ 0

noncomputable def rationalBands (J : ℕ) [NeZero J] (S : Finset RationalMode) : Finset (ZMod J) :=
  S.image fun b => (rationalFrequency J b.den b.num b.offset : ZMod J)

noncomputable def majorBands (J : ℕ) [NeZero J] (S : Finset ℤ) (T : Finset RationalMode) : Finset (ZMod J) :=
  S.image (fun k : ℤ => (k : ZMod J)) ∪ rationalBands J T

theorem eventually_major_bands_small {α : ℝ} (hα : 1 ≤ α) (S : Finset ℤ) (T : Finset RationalMode)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, ResidueTwoSidedScale α u →
      |frequencyCovariance α (scaleCutoff α u)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (majorBands (floorMul α (scaleCutoff α u)+1) S T)| ≤ ε*(scaleCutoff α u : ℝ) := by
  have hδS : 0 < ε/(2*(S.card+1)) := by positivity
  have hδT : 0 < ε/(2*(T.card+1)) := by positivity
  have hs := (eventually_all_finset S).mpr (fun k hk => eventually_fourier_term_small hα k hδS)
  have ht := (eventually_all_finset T).mpr (fun b hb =>
    eventually_rational_term_small hα b.den_pos b.num b.offset b.nonzero hδT)
  filter_upwards [hs, ht] with u huS huT
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
    change ‖covarianceFourierTerm α N R R (k : ZMod J)‖ ≤
      ε/(2*(S.card+1))*(J : ℝ)*(N : ℝ) at hh
    exact hh.trans_eq (by rw [div_mul_eq_div_div]; ring)
  have hT : (∑ k ∈ rationalBands J T, ‖F k‖) ≤ ε/2*(N : ℝ) := by
    apply image_norm_sum_bound T _ F (by positivity)
    intro b hb
    exact (huT b hb hrows).trans_eq (by dsimp only [N]; rw [div_mul_eq_div_div]; ring)
  have hh := union_norm_sum_bound _ _ F hS hT
  change |frequencyCovariance α N R R (majorBands J S T)| ≤ ε*(N : ℝ)
  unfold frequencyCovariance
  rw [sum_div]
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_sum_le _ _).trans
  change (∑ k ∈ majorBands J S T, ‖F k‖) ≤ _
  dsimp only [majorBands]
  linarith only [hh]

#print axioms eventually_rational_term_small
#print axioms eventually_major_bands_small
end Erdos972RationalBandFourierScales
