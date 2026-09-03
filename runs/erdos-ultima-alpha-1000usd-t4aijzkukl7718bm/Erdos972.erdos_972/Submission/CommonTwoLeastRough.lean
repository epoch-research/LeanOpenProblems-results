import Submission.PrimeTwoLeastFactorScales
import Submission.RoughSmoothAllParameters

/-! The sharper one-sided comparison and exact rough-output lower envelope
on one scale for every positive parameter. This does not prove a prime-pair
lower bound: the subtraction is explicitly nonpositive. -/
namespace Erdos972CommonTwoLeastRough

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972SelbergWeights Erdos972SelbergLowerMain Erdos972SelbergLowerTest
open Erdos972GrowingCoprimeCandidates Erdos972PrimePowerError
open Erdos972DualPrimeRows Erdos972ScaledPrimeRows Erdos972PolynomialRowScales
open Erdos972PrimeRotation Erdos972InverseGoodApproximation
open Erdos972PrimeRoughOutputs Erdos972PrimeAlmostPrime
open Erdos972SelbergMajorantSize Erdos972CappedLowerSieve
open Erdos972EfficientSieveScale Erdos972SharpReciprocalPrimeCost
open Erdos972EfficientPrimeAlmostPrime Erdos972PrimeLeastFactorScales
open Erdos972LeastFactorCutoff
open Erdos972RoughSmoothLowerBound Erdos972RoughSmoothComparison
open Erdos972PrimeTwoLeastFactorScales Erdos972RoughSmoothAllParameters

set_option maxHeartbeats 5000000
set_option exponentiation.threshold 8192
set_option autoImplicit false
attribute [local irreducible] root64

theorem exists_common_rough_twoLeast_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < fastRoot u ∧ B < layerCount u ∧
      2 ≤ Nat.sqrt (Nat.sqrt (root64 u)) ∧
      primeTwoLeastFactorMoment α (u^6) ≤ 1000000000*(u:ℝ)^6*Real.log (layerCutoff u) ∧
      (u:ℝ)^6/(roughConstant*(1+Real.log (u+1:ℕ))) ≤
        coprimePrimeWeight α (fastRoot u).factorial (u^6) := by
  have hmomentEvent :=
    (((nat_fourth_root_tendsto.comp root64_tendsto).eventually_ge_atTop 2).and
      ((layerCutoff_tendsto.eventually_ge_atTop ⌈α⌉₊).and
        (layerCount_tendsto.eventually_gt_atTop B)))
  have hmain := fastRoot_tendsto.eventually eventually_lowerMain_sixteen
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_rough_prime_budget.and ((root64_tendsto.eventually_ge_atTop 2048).and
      (hmain.and (fastRoot_tendsto.eventually_gt_atTop (max B (max 2 ⌈α⌉₊)))))).and
        hmomentEvent)
  let A := max T (B+1)
  obtain ⟨r, hr, hden⟩ := Erdos972RationalRoute.exists_good_approximant_large_den hα hI (A^4)
  let u := Nat.sqrt (Nat.sqrt r.den)
  have hAu : A ≤ u := (le_fourth_root_iff A r.den).mpr hden.le
  have hTu : T ≤ u := (le_max_left T (B+1)).trans hAu
  have hBu : B < u := by have := (le_max_right T (B+1)).trans hAu; omega
  obtain ⟨hu, hlo, hhi⟩ := fourth_root_bounds r.pos
  change 0 < u at hu
  change u^4 ≤ r.den at hlo
  change r.den ≤ 16*u^4 at hhi
  clear_value u
  obtain ⟨⟨⟨hψ, hbudget⟩, hv, hmainZ, hZbig⟩, hW, hαcut, hBJ⟩ := hT u hTu
  have hrows (d : ℕ) (hd : 0 < d) (hdv : d ≤ root64 u) :=
    prime_row_discrepancy α d (u^6) (input_divisor_row_discrepancy
      (show 0 ≤ α by linarith) r hr.le (K := 1) (by norm_num) (by simpa using hv)
      (root64_bounds hu).2.1 (by simpa using hlo) (by simpa using hhi) hd hdv le_rfl)
  have hαcutR : α ≤ layerCutoff u := (Nat.le_ceil α).trans (Nat.cast_le.mpr hαcut)
  have hmoment := prime_twoLeast_factor_bound hα.le hu hW hαcutR hbudget hrows
  obtain ⟨hZ, helig⟩ := fastRoot_eligible hu
  have hBZ : B < fastRoot u := (le_max_left B _).trans_lt hZbig
  have hZ2 : 2 ≤ fastRoot u := by
    exact (le_max_left 2 _).trans ((le_max_right B _).trans hZbig.le)
  have hαZ : α ≤ fastRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right 2 _).trans ((le_max_right B _).trans hZbig.le)))
  let Z := fastRoot u
  let R := Z^16
  have hR : 1 ≤ R := Nat.one_le_pow 16 Z hZ
  have hmod : R^2*Z ≤ root64 u := by
    apply le_trans _ helig
    exact Nat.mul_le_mul_right Z (Nat.pow_le_pow_right hR (by decide : 2 ≤ 3))
  have helig3 : R^3*Z ≤ root64 u := by
    apply le_trans _ helig
    exact Nat.mul_le_mul_right Z (Nat.pow_le_pow_right hR (by decide : 3 ≤ 3))
  have hE : 0 ≤ scaledRowError 1 u (root64 u)+
      (Chebyshev.psi (u^6 : ℕ)-Chebyshev.theta (u^6 : ℕ)) := by
    exact add_nonneg (scaledRowError_nonneg 1 u (root64 u))
      (sub_nonneg.mpr (Chebyshev.theta_le_psi _))
  have hcap : ∀ n ∈ Ioc 0 (u^6), (floorMul α n).Coprime Z.factorial →
      Erdos972PairSieve.majorant R (floorMul α n) ≤ majorantCap 49153 := by
    intro n hn hc
    obtain ⟨hn0, hnN⟩ := mem_Ioc.mp hn
    have hfpos : 0 < floorMul α n := by
      apply Nat.floor_pos.mpr
      have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn0
      calc
        (1:ℝ) = 1*1 := by norm_num
        _ ≤ α*n := mul_le_mul hα.le hnR (by norm_num) (by linarith only [hα])
    apply majorant_bounded_factors hR hfpos.ne'
    exact factor_length_bound hfpos hZ2 hc
      (fast_floor_output_power_bound hαZ hZ2 hnN)
  have hlower := rough_weight_log_lower (Ioc 0 (u^6)) primeWeight (floorMul α)
    (fun n _ => primeWeight_nonneg n) hR hZ helig3 hE (majorantCap_pos _) hψ
    hmainZ hbudget hcap
    (fun d hd hdR => prime_row_discrepancy α d (u^6) (input_divisor_row_discrepancy
      (show 0 ≤ α by linarith) r hr.le (K := 1) (by norm_num) (by simpa using hv)
      (root64_bounds hu).2.1 (by simpa using hlo) (by simpa using hhi)
      hd (hdR.trans hmod) le_rfl))
  rw [rough_prime_sum] at hlower
  have hR3 : R^3 ≤ root64 u := (Nat.le_mul_of_pos_right _ hZ).trans helig
  clear_value R
  have hRR3 : R ≤ R^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hR (show 1 ≤ 3 by decide)
  have hvu : root64 u ≤ u := by
    have hh : root64 u ≤ (root64 u)^64 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (root64_bounds hu).1 (show 1 ≤ 64 by decide)
    exact hh.trans (root64_bounds hu).2.1
  have hRu : R ≤ u := hRR3.trans (hR3.trans hvu)
  refine ⟨u, hBu, hBZ, hBJ, hW, hmoment, ?_⟩
  apply le_trans _ hlower
  rw [Nat.cast_pow]
  have hC := majorantCap_pos 49153
  have hL : 0 < 1+Real.log (R+1:ℕ) := by linarith only [Real.log_natCast_nonneg (R+1)]
  have h24C : 0 < 24*majorantCap 49153 := mul_pos (by norm_num) hC
  change (u:ℝ)^6/(24*majorantCap 49153*(1+Real.log (u+1:ℕ))) ≤ _
  apply div_le_div_of_nonneg_left (by positivity) (mul_pos h24C hL)
  exact mul_le_mul_of_nonneg_left (add_le_add_right
    (Erdos972ExponentialSum.monotone_log_natCast (Nat.add_le_add_right hRu 1)) 1)
    h24C.le


noncomputable def twoLeastRoughError (τ : ℝ) (u : ℕ) : ℝ :=
  1000000000*roughParameter τ u*(u:ℝ)^6*Real.log (layerCutoff u)

/-- The exact lower envelope remains below the sharper budget for EVERY
positive parameter. This compares two bounds, not the actual error. -/
theorem lower_envelope_lt_twoLeast_budget {τ : ℝ} (hτ : 0 < τ) {u : ℕ}
    (hZ : 2 ≤ fastRoot u) (hW : 2 ≤ Nat.sqrt (Nat.sqrt (root64 u))) :
    exactRoughCoefficient τ*(u:ℝ)^6 < twoLeastRoughError τ u := by
  have hZu : fastRoot u ≤ u :=
    (root64_le_self _).trans (root64_le_self u)
  have hu : 0 < u := by omega
  have hN : (0:ℝ) < (u:ℝ)^6 := pow_pos (Nat.cast_pos.mpr hu) _
  have hz : 0 < Real.log (fastRoot u) := Real.log_pos (by exact_mod_cast hZ)
  have hL : 0 < Real.log (layerCutoff u) := Erdos972LeastFactorSieve.log_logLevel_pos _
  have ht : 0 < roughParameter τ u := div_pos hτ hz
  have heq : roughParameter τ u*Real.log (fastRoot u) = τ := div_mul_cancel₀ τ hz.ne'
  have hlog : Real.log (fastRoot u) ≤ 832*Real.log (layerCutoff u) := by
    have hh := (Erdos972ExponentialSum.monotone_log_natCast hZu).trans
      (Erdos972ExponentialSum.monotone_log_natCast (layerCutoff_bounds hu hW).2)
    dsimp only at hh
    rw [Nat.cast_pow, Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have hm := mul_le_mul_of_nonneg_left hlog (mul_nonneg ht.le hN.le)
  have hpos : 0 < roughParameter τ u*(u:ℝ)^6*Real.log (layerCutoff u) := by positivity
  have hl := mul_le_mul_of_nonneg_right (exactRoughCoefficient_le hτ) hN.le
  unfold twoLeastRoughError
  nlinarith only [hm, hpos, hl, congrArg (fun x : ℝ => x*(u:ℝ)^6) heq]

lemma twoLeast_rough_comparison {α τ : ℝ} (hτ : 0 < τ) {u : ℕ}
    (hZ : 2 ≤ fastRoot u)
    (hbound : primeTwoLeastFactorMoment α (u^6) ≤
      1000000000*(u:ℝ)^6*Real.log (layerCutoff u)) :
    mixedPrimeSmooth (roughParameter τ u) α (u^6)-twoLeastRoughError τ u ≤
      mixedPrimeMangoldt α (u^6) := by
  have ht : 0 < roughParameter τ u := div_pos hτ (Real.log_pos (by exact_mod_cast hZ))
  have hh := mixed_smooth_upper_twoLeast ht α (u^6)
  have hm := mul_le_mul_of_nonneg_left hbound ht.le
  unfold twoLeastRoughError
  nlinarith only [hh, hm]

/-- All parameters concern one actual irrational good scale, not independently
chosen scales for the upper and lower estimates. -/
theorem exists_all_parameter_twoLeast_estimates {α : ℝ}
    (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < layerCount u ∧ 2 ≤ fastRoot u ∧ α ≤ fastRoot u ∧
      ∀ τ : ℝ, 0 < τ →
        exactRoughCoefficient τ*(u:ℝ)^6 ≤ mixedPrimeSmooth (roughParameter τ u) α (u^6) ∧
        mixedPrimeSmooth (roughParameter τ u) α (u^6)-twoLeastRoughError τ u ≤
          mixedPrimeMangoldt α (u^6) ∧
        exactRoughCoefficient τ*(u:ℝ)^6 < twoLeastRoughError τ u := by
  let B' := max B (max 2 ⌈α⌉₊)
  obtain ⟨u, hu, hZ, hJ, hW, hmoment, hweight⟩ := exists_common_rough_twoLeast_scale hα hI B'
  have hZ2 : 2 ≤ fastRoot u :=
    (le_max_left 2 _).trans ((le_max_right B _).trans hZ.le)
  have hαZ : α ≤ fastRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right 2 _).trans ((le_max_right B _).trans hZ.le)))
  refine ⟨u, (le_max_left _ _).trans_lt hu, (le_max_left _ _).trans_lt hJ, hZ2, hαZ, ?_⟩
  intro τ hτ
  exact ⟨rough_weight_to_smooth_exp hα hZ2 hαZ hweight hτ,
    twoLeast_rough_comparison hτ hZ2 hmoment,
    lower_envelope_lt_twoLeast_budget hτ hZ2 hW⟩

#print axioms exists_common_rough_twoLeast_scale
#print axioms lower_envelope_lt_twoLeast_budget
#print axioms exists_all_parameter_twoLeast_estimates
end Erdos972CommonTwoLeastRough
