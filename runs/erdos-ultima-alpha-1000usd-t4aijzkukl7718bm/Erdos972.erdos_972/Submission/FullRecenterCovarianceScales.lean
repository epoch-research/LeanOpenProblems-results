import Submission.RecenterCovarianceScales

/-! The common recentering scales with their actual dual and joint rows
retained, so further arithmetic estimates can use the very same scales. -/
namespace Erdos972FullRecenterCovarianceScales

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius
open Erdos972PrimePowerError Erdos972PolynomialRowScales Erdos972CenteredRowScales
open Erdos972GrowingTypeI Erdos972GrowingTypeIIReduction Erdos972CovarianceScaleBudgets
open Erdos972WeightedPrimeRotation Erdos972BeattyRows Erdos972DualPrimeRows
open Erdos972ScaledPrimeRows Erdos972OriginalTypeICovariance Erdos972DualTypeICovariance
open Erdos972TypeICovariance Erdos972LogarithmicCovariance Erdos972DoubleVaughan
open Erdos972WeightedBeattyRows Erdos972CommonCovarianceScales
open Erdos972RecenterCovarianceBounds Erdos972DivisorMeanRecenter
open Erdos972MobiusPartialSums Erdos972MobiusLaplace Erdos972CenteredDoubleVaughan
open Erdos972RecenterCovarianceScales Erdos972DivisorPairCount

set_option maxHeartbeats 2000000
attribute [local irreducible] root64

def FullTwoSidedScale (α : ℝ) (u : ℕ) : Prop :=
  (∀ e : ℕ, 0 < e → e ≤ root64 u → ∀ X : ℕ, X ≤ u^6 →
    |inputDivisorRow α e X-Chebyshev.psi X/e| ≤ scaledRowError (dualScaleLoss α) u (root64 u)) ∧
  (∀ d e : ℕ, 0 < d → 0 < e → e ≤ root64 u → ∀ X ≤ scaleCutoff α u,
    |((divisorPairs α X d e).card : ℝ)-(X : ℝ)/(d*e)| ≤ 118*(root64 u : ℝ)*(u : ℝ)^4)

/-- All four conclusions use the very same row hypotheses, obtained by a
single invocation of the two-sided scale theorem. -/
theorem exists_full_recenter_covariance_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u N : ℕ, B < u ∧ N = scaleCutoff α u ∧ B < growingCutoff u ∧ root64 u ≤ N ∧
      OutputPrimeScale α u ∧ FullTwoSidedScale α u ∧
      |covariance N (fun n => typeIPart (growingCutoff u) (growingCutoff u) n)
        (fun n => vonMangoldt (floorMul α n))| ≤ ε*N ∧
      |covariance N (fun n => vonMangoldt n)
        (fun n => typeIPart (growingCutoff u) (growingCutoff u) (floorMul α n))| ≤ ε*N ∧
      |covariance N (fun n => typeIPart (growingCutoff u) (growingCutoff u) n)
        (fun n => typeIPart (growingCutoff u) (growingCutoff u) (floorMul α n))| ≤ ε*N ∧
      |meanCenteredFourFactor α N (growingCutoff u) (growingCutoff u) (growingCutoff u) (growingCutoff u)-
        centeredFourFactor α N (growingCutoff u) (growingCutoff u) (growingCutoff u) (growingCutoff u)| ≤ ε*N := by
  have hsmall : 0 < ε/8 := by positivity
  have hm_event : ∀ᶠ u : ℕ in atTop, |reciprocalMoebius (growingCutoff u)| ≤ 1 := by
    have hh := (reciprocalMoebius_tendsto_zero.comp growingCutoff_tendsto).abs
    simp only [abs_zero] at hh
    exact ((tendsto_order.mp hh).2 1 (by norm_num)).mono (fun _ h => h.le)
  have hevent := (eventually_original_covariance_budget hα.le hsmall).and
    ((eventually_dual_covariance_budget hα.le hsmall).and
      ((eventually_double_typeI_budget hα.le hsmall).and
        ((growingCutoff_tendsto.eventually_gt_atTop B).and hm_event)))
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  obtain ⟨u, hu, hαu, hv, hrows, hdual, hdiv⟩ := exists_two_sided_prime_divisor_scale hα hI (max B T)
  obtain ⟨hl, hr, hd, hcut, hm⟩ := hT u ((le_max_right B T).trans hu.le)
  have hu0 : 0 < u := (Nat.zero_le _).trans_lt hu
  have hαu' : α ≤ u := by linarith only [hα, hαu]
  obtain ⟨huN, hNu, _⟩ := scaleCutoff_bounds hα.le hu0 hαu'
  have hvN : root64 u ≤ scaleCutoff α u := (root64_le u).trans huN
  have hcut0 : 0 < growingCutoff u := (Nat.zero_le B).trans_lt hcut
  have helig := (growingCutoff_eligible u).2
  have helig1 : 1*growingCutoff u ≤ root64 u := by
    simpa only [one_mul] using (growingCutoff_eligible u).1
  have hE0 : 0 ≤ polynomialRowError u (root64 u) := by
    unfold polynomialRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u]
  have hEp0 : 0 ≤ scaledRowError (dualScaleLoss α) u (root64 u) := by
    unfold scaledRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos (256*dualScaleLoss α), Real.log_natCast_nonneg u]
  have hEd0 : 0 ≤ 118*(root64 u : ℝ)*(u : ℝ)^4 := by positivity
  let N := scaleCutoff α u
  let v := root64 u
  let W := growingCutoff u
  let L := 1+Real.log (α*N)
  let E₁ := 200*(v : ℝ)*L^3*(polynomialRowError u v+1)+2*|Erdos972RealLogCenter.commonLogCenter (α*N)|/α
  let E₂ := 2*|covariance N (fun n => vonMangoldt n) (fun n => Real.log n)|+
    50*(v : ℝ)*L^3*(scaledRowError (dualScaleLoss α) u v+118*(v : ℝ)*(u : ℝ)^4+1)
  let E := 100*(118*(v : ℝ)*(u : ℝ)^4+1)*(v : ℝ)^2*L^5
  have hleft (U V : ℕ) (hU : 0 < U) (hV : 0 < V) (hUV : U*V ≤ v) :
      |covariance N (fun n => typeIPart U V n) (fun n => vonMangoldt (floorMul α n))| ≤ E₁ := by
    apply original_typeI_covariance_bound hα hI hE0 hU hV hUV hvN
    intro m hm hmv X hX
    rw [outputRow_mangoldt]
    exact hrows m hm hmv X (hX.trans (scaleCutoff_row_eligible hα.le u m (scaleCutoff α u/m) le_rfl))
  have hright (S T : ℕ) (hS : 0 < S) (hT : 0 < T) (hST : S*T ≤ v) :
      |covariance N (fun n => vonMangoldt n) (fun n => typeIPart S T (floorMul α n))| ≤ E₂ := by
    apply dual_typeI_covariance_bound hα.le hS hT hST hvN hEp0 hEd0
    · intro j hj e he
      exact hdual e (mem_Ioc.mp he).1 ((mem_Ioc.mp he).2.trans hST) j (hj.trans hNu)
    · intro j hj a ha b hb
      exact hdiv a b (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1 ((mem_Ioc.mp hb).2.trans hST) j hj
  have hjoint (U V S T : ℕ) (hU : 0 < U) (hV : 0 < V) (hS : 0 < S) (hT : 0 < T)
      (hUV : U*V ≤ v) (hST : S*T ≤ v) :
      |covariance N (fun n => typeIPart U V n) (fun n => typeIPart S T (floorMul α n))| ≤
        32*(N : ℝ)*|reciprocalMoebius U*reciprocalMoebius S|+E := by
    apply typeI_covariance_bound hα.le hU hV hS hT hUV hST hvN hEd0
    intro j hj a ha b hb
    exact hdiv a b (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1 ((mem_Ioc.mp hb).2.trans hST) j hj
  have hL : 1 ≤ L := (scale_log_bound hα.le hu0 hαu').1
  have hN0 : 0 < N := hu0.trans_le huN
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN0
  have hLN : Real.log N ≤ L-1 := by
    have hh := Real.log_le_log hNR (le_mul_of_one_le_left hNR.le hα.le)
    dsimp only [L]
    linarith only [hh]
  have hLg : Real.log (floorMul α N) ≤ L-1 := by
    have hh := log_floorMul_le hα.le (mem_Ioc.mpr ⟨hN0, le_rfl⟩)
    dsimp only [L]
    linarith only [hh]
  have hE : 0 ≤ E := by dsimp only [E]; positivity [hL]
  have hBA := hjoint 1 W W W (by norm_num) hcut0 hcut0 hcut0 helig1 helig
  have hAB := hjoint W W 1 W hcut0 hcut0 (by norm_num) hcut0 helig helig1
  have hBB := hjoint 1 W 1 W (by norm_num) hcut0 (by norm_num) hcut0 helig1 helig1
  simp only [reciprocalMoebius_one, one_mul, mul_one, abs_one] at hBA hAB hBB
  have hc := mean_recenter_covariance_bound hα.le hcut0 helig hvN hL hLN hLg hm hE
    (hleft 1 W (by norm_num) hcut0 helig1) (hright 1 W (by norm_num) hcut0 helig1) hBA hAB hBB
  have hsmallcut : 210*(v : ℝ)^2*L^2 ≤ 3*E := by
    have hp := pow_le_pow_right₀ hL (show 2 ≤ 5 by norm_num)
    have hpower := mul_le_mul_of_nonneg_left hp (show 0 ≤ 210*(v : ℝ)^2 by positivity)
    have hnonneg : 0 ≤ (118*(v : ℝ)*(u : ℝ)^4)*(v : ℝ)^2*L^5 := by positivity [hL]
    have hnonneg' : 0 ≤ (v : ℝ)^2*L^5 := by positivity [hL]
    dsimp only [E]
    nlinarith only [hpower, hnonneg, hnonneg']
  change E₁ ≤ ε/8*N at hl
  change E₂ ≤ ε/8*N at hr
  change 32*(N : ℝ)*|reciprocalMoebius W*reciprocalMoebius W|+E ≤ ε/8*N at hd
  have hlarge : ε/8*N ≤ ε*N := by nlinarith only [hε, hNR]
  refine ⟨u, N, (le_max_left B T).trans_lt hu, rfl, hcut, hvN, hrows, ⟨hdual, hdiv⟩,
    (hleft W W hcut0 hcut0 helig).trans (hl.trans hlarge),
    (hright W W hcut0 hcut0 helig).trans (hr.trans hlarge),
    (hjoint W W W W hcut0 hcut0 hcut0 hcut0 helig helig).trans (hd.trans hlarge), ?_⟩
  change |meanCenteredFourFactor α N W W W W-centeredFourFactor α N W W W W| ≤ ε*N
  have hsq : |reciprocalMoebius W*reciprocalMoebius W| = (reciprocalMoebius W)^2 := by
    rw [← pow_two, abs_sq]
  rw [hsq] at hd
  have hnonneg : 0 ≤ (N : ℝ)*(reciprocalMoebius W)^2 := by positivity
  change |meanCenteredFourFactor α N W W W W-centeredFourFactor α N W W W W| ≤
    E₁+E₂+96*(N : ℝ)*(reciprocalMoebius W)^2+3*E+210*(v : ℝ)^2*L^2 at hc
  nlinarith only [hc, hsmallcut, hl, hr, hd, hnonneg]

#print axioms exists_full_recenter_covariance_scale

end Erdos972FullRecenterCovarianceScales
