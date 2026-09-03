import Submission.PrimeFactorDiagonalScales

/-! Common scale selection with both Type-I orientations, removal of
proper-prime-power factors, and removal of the equal-prime-factor diagonal.
The distinct-prime-factor off-diagonal is still not bounded from below. -/
namespace Erdos972CommonPrimeOffDiagonal

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972CommonAsymmetricDiagonal Erdos972CommonCovarianceScales
open Erdos972PrimeFactorDiagonalScales Erdos972AsymmetricDiagonalBudget
open Erdos972FourFactorDiagonalSplit Erdos972PrimeFactorError Erdos972PrimeFactorErrorScales
open Erdos972VaughanDiagonalBound Erdos972AsymmetricTypeIScales
open Erdos972CovarianceScaleBudgets Erdos972TypeICovarianceScales
open Erdos972PolynomialRowScales Erdos972CenteredRowScales
open Erdos972GrowingTypeI Erdos972DualPrimeRows Erdos972ScaledPrimeRows
open Erdos972LogarithmicCovariance Erdos972DoubleVaughan Erdos972PrimePowerError
open Erdos972OriginalTypeICovariance Erdos972DualTypeICovariance Erdos972TypeICovariance
open Erdos972WeightedBeattyRows Erdos972WeightedPrimeRotation Erdos972BeattyRows
open Erdos972ReciprocalDivisorCounts Erdos972DivisorCovariance
open Erdos972RationalRotationCount Erdos972InverseGoodApproximation
open Erdos972DirectRowApproximation Erdos972DivisorPairCount
set_option maxHeartbeats 1500000
attribute [local irreducible] root64

lemma fourFactor_prime_offDiagonal_identity {α : ℝ} (hα : 1 ≤ α) (N U V : ℕ) :
    fourFactorRemainder α N U V U V - primeFactorOffDiagonal α N U V =
      primeVaughanDiagonal α N U V + primeFactorError α N U V := by
  rw [← typeII_pair_eq_fourFactor hα]
  unfold primeFactorError
  rw [prime_remainder_diagonal_split hα]
  ring

/-- The diagonal estimate is selected together with both prime-row families
and the joint small-divisor estimates, not on an unrelated sequence. -/
theorem exists_two_sided_scale_small_prime_diagonal {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < mobiusCutoff u ∧ 4*α ≤ u ∧
      2048*dualScaleLoss α ≤ root64 u ∧ OutputPrimeScale α u ∧
      (∀ e : ℕ, 0 < e → e ≤ root64 u → ∀ X : ℕ, X ≤ u^6 →
        |inputDivisorRow α e X-Chebyshev.psi X/e| ≤ scaledRowError (dualScaleLoss α) u (root64 u)) ∧
      (∀ d e : ℕ, 0 < d → 0 < e → e ≤ root64 u → ∀ X ≤ scaleCutoff α u,
        |((divisorPairs α X d e).card : ℝ)-(X : ℝ)/(d*e)| ≤ 118*(root64 u : ℝ)*(u : ℝ)^4) ∧
      |primeVaughanDiagonal α (scaleCutoff α u) (mobiusCutoff u) (mangoldtCutoff u)| ≤
        ε*(scaleCutoff α u : ℝ) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_small_prime_diagonal hα.le hε).and (mobiusCutoff_tendsto.eventually_gt_atTop B))
  let K := dualScaleLoss α
  have hK : 0 < K := dualScaleLoss_pos hα.le
  let C := max (max B T) (max (⌈4*α⌉₊+1) ((2048*K)^64))
  obtain ⟨u, v, r, hu, hv, hvu, huv, rfl, hr, hlo, hhi, hrows⟩ :=
    exists_polynomial_beatty_arc_scale_data hα hI C
  have hu0 : 0 < u := (Nat.zero_le C).trans_lt hu
  have hTu : T ≤ u := (le_max_right B T).trans ((le_max_left _ _).trans hu.le)
  obtain ⟨hdiag, hcut⟩ := hT u hTu
  have hαu : 4*α ≤ u := (Nat.le_ceil _).trans (by
    exact_mod_cast (Nat.le_succ ⌈4*α⌉₊).trans
      ((le_max_left (⌈4*α⌉₊+1) ((2048*K)^64)).trans ((le_max_right (max B T) _).trans hu.le)))
  have hKu : (2048*K)^64 ≤ u :=
    (le_max_right (⌈4*α⌉₊+1) _).trans ((le_max_right (max B T) _).trans hu.le)
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
  obtain ⟨a, q, hq0, haq, hqlo, hqhi, hqa, hNsq⟩ := inverse_diagonal_data hα.le r hr hu0 hαu hlo hhi
  refine ⟨u, (le_max_left B T).trans_lt ((le_max_left _ _).trans_lt hu), hcut,
    hαu, hKv, hrows, ?_, ?_, hdiag a q hq0 haq hqlo hqhi hqa hNsq⟩
  · intro e he hev X hX
    exact input_divisor_row_discrepancy (by linarith : 0 ≤ α) s hs hK hKv hvu hslo' hshi' he hev hX
  · intro d e hd he hev X hX
    apply reciprocal_scale_divisor_prefix_bound hα.le r hr hu0
      (show 0 < root64 u by omega) hαu hlo hhi _ hd he hev
    have hα0 : 0 < α := by linarith
    have hh : (scaleCutoff α u : ℝ) ≤ (u : ℝ)^6/α := Nat.floor_le (by positivity)
    have hXR : (X : ℝ) ≤ scaleCutoff α u := Nat.cast_le.mpr hX
    have hh' := (le_div_iff₀ hα0).mp (hXR.trans hh)
    nlinarith only [hh']

/-- The three Type-I errors and the replacement of the entire four-factor
remainder by its distinct-prime-factor off-diagonal are small at one scale. -/
theorem exists_typeI_and_prime_offDiagonal_scale {α : ℝ}
    (hα : 1 < α) (hI : Irrational α) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u N : ℕ, B < u ∧ N = scaleCutoff α u ∧ B < mobiusCutoff u ∧ root64 u ≤ N ∧
      mobiusCutoff u * mangoldtCutoff u ≤ root64 u ∧ OutputPrimeScale α u ∧
      |covariance N (fun n => typeIPart (mobiusCutoff u) (mangoldtCutoff u) n)
        (fun n => vonMangoldt (floorMul α n))| ≤ ε*N ∧
      |covariance N (fun n => vonMangoldt n)
        (fun n => typeIPart (mobiusCutoff u) (mangoldtCutoff u) (floorMul α n))| ≤ ε*N ∧
      |covariance N (fun n => typeIPart (mobiusCutoff u) (mangoldtCutoff u) n)
        (fun n => typeIPart (mobiusCutoff u) (mangoldtCutoff u) (floorMul α n))| ≤ ε*N ∧
      |fourFactorRemainder α N (mobiusCutoff u) (mangoldtCutoff u)
        (mobiusCutoff u) (mangoldtCutoff u) -
        primeFactorOffDiagonal α N (mobiusCutoff u) (mangoldtCutoff u)| ≤ ε*N := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_original_covariance_budget hα.le hε).and
      ((eventually_dual_covariance_budget hα.le hε).and
        ((eventually_asymmetric_double_budget hα.le hε).and
          (eventually_small_prime_factor_error hα.le (show 0 < ε/2 by positivity)))))
  obtain ⟨u, hu, hcut, hαu, hv, hrows, hdual, hdiv, hdiag⟩ :=
    exists_two_sided_scale_small_prime_diagonal hα hI (show 0 < ε/2 by positivity) (max B T)
  obtain ⟨hl, hr, hd, hpower⟩ := hT u ((le_max_right B T).trans hu.le)
  have hu0 : 0 < u := (Nat.zero_le _).trans_lt hu
  have hαu' : α ≤ u := by linarith only [hα, hαu]
  obtain ⟨huN, hNu, _⟩ := scaleCutoff_bounds hα.le hu0 hαu'
  have hvN : root64 u ≤ scaleCutoff α u := (root64_le u).trans huN
  obtain ⟨hU0, helig, hUu⟩ := asymmetric_cutoffs_bounds hu0
  have hV0 : 0 < mangoldtCutoff u := by unfold mangoldtCutoff; positivity
  have hE0 : 0 ≤ polynomialRowError u (root64 u) := by
    unfold polynomialRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u]
  have hEp0 : 0 ≤ scaledRowError (dualScaleLoss α) u (root64 u) := by
    unfold scaledRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos (256*dualScaleLoss α), Real.log_natCast_nonneg u]
  have hEd0 : 0 ≤ 118*(root64 u : ℝ)*(u : ℝ)^4 := by positivity
  refine ⟨u, scaleCutoff α u, (le_max_left B T).trans_lt hu, rfl,
    (le_max_left B T).trans_lt hcut, hvN, helig, hrows, ?_, ?_, ?_, ?_⟩
  · have hh := original_typeI_covariance_bound hα hI hE0 hU0 hV0 helig hvN (by
      intro m hm hmv X hX
      rw [outputRow_mangoldt]
      exact hrows m hm hmv X (hX.trans (scaleCutoff_row_eligible hα.le u m (scaleCutoff α u/m) le_rfl)))
    exact hh.trans hl
  · have hh := dual_typeI_covariance_bound hα.le hU0 hV0 helig hvN hEp0 hEd0 (by
      intro j hj e he
      exact hdual e (mem_Ioc.mp he).1 ((mem_Ioc.mp he).2.trans helig) j (hj.trans hNu)) (by
      intro j hj a ha b hb
      exact hdiv a b (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1 ((mem_Ioc.mp hb).2.trans helig) j hj)
    exact hh.trans hr
  · have hh := typeI_covariance_bound hα.le hU0 hV0 hU0 hV0 helig helig hvN hEd0 (by
      intro j hj a ha b hb
      exact hdiv a b (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1 ((mem_Ioc.mp hb).2.trans helig) j hj)
    exact hh.trans hd

  · rw [fourFactor_prime_offDiagonal_identity hα.le]
    exact (abs_add_le _ _).trans ((add_le_add hdiag hpower).trans_eq (by ring))

#print axioms fourFactor_prime_offDiagonal_identity
#print axioms exists_two_sided_scale_small_prime_diagonal
#print axioms exists_typeI_and_prime_offDiagonal_scale
end Erdos972CommonPrimeOffDiagonal
