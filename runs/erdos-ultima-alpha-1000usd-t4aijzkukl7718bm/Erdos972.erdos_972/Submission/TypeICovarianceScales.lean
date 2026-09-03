import Submission.TypeICovariance

/-! Sublinear two-Type-I covariance on common rational-approximation scales. -/
namespace Erdos972TypeICovarianceScales

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972TypeICovariance Erdos972DivisorCovariance Erdos972PrimePowerError
open Erdos972LogarithmicCovariance Erdos972DoubleVaughan Erdos972PolynomialRowScales
open Erdos972CenteredRowScales Erdos972GrowingTypeI Erdos972GrowingTypeIIReduction
open Erdos972MobiusPartialSums Erdos972MobiusLaplace Erdos972DivisorPairCount
open Erdos972WeightedPrimeRotation Erdos972BeattyRows

set_option maxHeartbeats 1000000

lemma eventually_covariance_budget {α : ℝ} (hα : 1 ≤ α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      100*(118*(root64 u : ℝ)*(u : ℝ)^4+1)*(root64 u : ℝ)^2*
        (1+Real.log (α*scaleCutoff α u))^5 ≤ ε*(scaleCutoff α u : ℝ) := by
  have hα0 : 0 < α := by linarith
  let C : ℝ := 100*119*6^5
  have hh := (squared_family_divisor_error_tendsto 5).const_mul C
  simp only [mul_zero] at hh
  filter_upwards [(tendsto_order.mp hh).2 (ε/(2*α)) (by positivity),
    eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊] with u hu hu0 huα
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu0
  have huR1 : (1 : ℝ) ≤ u := by exact_mod_cast hu0
  have hvR : (1 : ℝ) ≤ root64 u := by exact_mod_cast (root64_bounds hu0).1
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  obtain ⟨huN, hNu, hscale⟩ := scaleCutoff_bounds hα hu0 hαu
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr (hu0.trans huN)
  have hy1 : 1 ≤ α*scaleCutoff α u := one_le_mul_of_one_le_of_one_le hα (by exact_mod_cast hu0.trans huN)
  have hNuR : α*scaleCutoff α u ≤ (u : ℝ)^6 := by
    have hh : (scaleCutoff α u : ℝ) ≤ (u : ℝ)^6/α := Nat.floor_le (by positivity)
    nlinarith only [(le_div_iff₀ hα0).mp hh]
  have hlog : 1+Real.log (α*scaleCutoff α u) ≤ 6*(1+Real.log u) := by
    have hh := Real.log_le_log (show 0 < α*scaleCutoff α u by positivity) hNuR
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh]
  have hB : 118*(root64 u : ℝ)*(u : ℝ)^4+1 ≤ 119*(root64 u : ℝ)*(u : ℝ)^4 := by
    have hp : 1 ≤ (root64 u : ℝ)*(u : ℝ)^4 := one_le_mul_of_one_le_of_one_le hvR (one_le_pow₀ huR1)
    nlinarith only [hp]
  have hbudget : 100*(118*(root64 u : ℝ)*(u : ℝ)^4+1)*(root64 u : ℝ)^2*
      (1+Real.log (α*scaleCutoff α u))^5 ≤
        C*(root64 u : ℝ)^3*(1+Real.log u)^5*(u : ℝ)^4 := by
    have hp := pow_le_pow_left₀ (by linarith [Real.log_nonneg hy1]) hlog 5
    have hm := mul_le_mul (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 100)) (sq_nonneg (root64 u : ℝ))) hp
      (by positivity [Real.log_nonneg hy1]) (by positivity)
    exact hm.trans_eq (by dsimp [C]; ring)
  have hsmall : C*(root64 u : ℝ)^3*(1+Real.log u)^5 ≤ (ε/(2*α))*(u : ℝ)^2 := by
    rw [← mul_div_assoc] at hu
    simpa only [mul_assoc] using ((div_lt_iff₀ (sq_pos_of_pos huR)).mp hu).le
  have hm := mul_le_mul_of_nonneg_right hsmall (pow_nonneg huR.le 4)
  have hs := mul_le_mul_of_nonneg_left hscale (show 0 ≤ ε/(2*α) by positivity)
  have he : (ε/(2*α))*(2*α*scaleCutoff α u) = ε*scaleCutoff α u := by field_simp
  rw [he] at hs
  nlinarith only [hbudget, hm, hs]

lemma growing_slope_product_tendsto :
    Tendsto (fun u : ℕ => 32*|reciprocalMoebius (growingCutoff u)*reciprocalMoebius (growingCutoff u)|)
      atTop (𝓝 0) := by
  have hh := reciprocalMoebius_tendsto_zero.comp growingCutoff_tendsto
  simpa using ((hh.mul hh).abs.const_mul 32)

/-- The covariance bound is genuinely sublinear with both Vaughan cutoffs
growing. The prime-output arc estimates are retained at exactly the same scale. -/
theorem exists_growing_typeI_covariance_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u N : ℕ, B < u ∧ N = scaleCutoff α u ∧ B < growingCutoff u ∧ root64 u ≤ N ∧
      (∀ m : ℕ, 0 < m → m ≤ root64 u → ∀ X : ℕ, X ≤ u^6 →
        |mangoldtArcSum (1/(α*m)) (-rowArcLeft (α*m)) (rowArcLeft (α*m)) (1-rowArcLeft (α*m)) X-
          (1/(α*m))*Chebyshev.psi X| ≤ polynomialRowError u (root64 u)) ∧
      |covariance N (fun n => typeIPart (growingCutoff u) (growingCutoff u) n)
        (fun n => typeIPart (growingCutoff u) (growingCutoff u) (floorMul α n))| ≤ ε*N := by
  have hevent := eventually_covariance_budget hα.le (show 0 < ε/2 by positivity)
  have hmain := (tendsto_order.mp growing_slope_product_tendsto).2 (ε/2) (by positivity)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hevent.and (hmain.and (growingCutoff_tendsto.eventually_gt_atTop B)))
  obtain ⟨u, hu, hαu, hv, hrows, hdiv⟩ := exists_joint_prime_divisor_scale hα hI (max B T)
  obtain ⟨he, hm, hcut⟩ := hT u ((le_max_right B T).trans hu.le)
  have hu0 : 0 < u := (Nat.zero_le _).trans_lt hu
  have hαu' : α ≤ u := by linarith only [hα, hαu]
  have huN := (scaleCutoff_bounds hα.le hu0 hαu').1
  have hvN : root64 u ≤ scaleCutoff α u := (root64_le u).trans huN
  have hcut0 : 0 < growingCutoff u := (Nat.zero_le B).trans_lt hcut
  have helig := (growingCutoff_eligible u).2
  have hb := typeI_covariance_bound hα.le hcut0 hcut0 hcut0 hcut0 helig helig hvN
    (by positivity : 0 ≤ 118*(root64 u : ℝ)*(u : ℝ)^4) (by
      intro j hj a ha b hb
      exact hdiv a b (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1 ((mem_Ioc.mp hb).2.trans helig) j hj)
  refine ⟨u, scaleCutoff α u, (le_max_left B T).trans_lt hu, rfl, hcut, hvN, hrows, ?_⟩
  have hm' := mul_le_mul_of_nonneg_right hm.le (Nat.cast_nonneg (α := ℝ) (scaleCutoff α u))
  nlinarith only [hb, he, hm']

#print axioms exists_growing_typeI_covariance_scale

end Erdos972TypeICovarianceScales
