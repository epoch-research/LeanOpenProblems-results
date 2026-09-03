import Submission.RoughSmoothComparison

/-!
A single direct-approximation scale supports both the efficient rough-output
lower bound and the least-factor moment bound. This removes an existential
scale-selection ambiguity but does not improve either numerical bound.
-/
namespace Erdos972CommonRoughMomentScale

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

set_option maxHeartbeats 5000000
set_option exponentiation.threshold 8192

theorem exists_common_rough_moment_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < fastRoot u ∧ B < layerCount u ∧
      primeLeastFactorMoment α (u^6) ≤ 100000*(u:ℝ)^6*(layerCount u+1) ∧
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
  have hmoment := prime_least_factor_bound hα.le hu hW hαcutR hbudget hrows
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
  refine ⟨u, hBu, hBZ, hBJ, hmoment, ?_⟩
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


/-- Finite transfer from the actual rough-weight lower bound, with the
choice of smoothing parameter made only after the scale is fixed. -/
theorem rough_weight_to_smooth {α : ℝ} (hα : 1 < α) {u : ℕ}
    (hZ2 : 2 ≤ fastRoot u) (hαZ : α ≤ fastRoot u)
    (hweight : (u:ℝ)^6/(roughConstant*(1+Real.log (u+1:ℕ))) ≤
      coprimePrimeWeight α (fastRoot u).factorial (u^6))
    {τ : ℝ} (hτ : 0 < τ) (hτsmall : τ ≤ 1/2) :
    roughSmoothCoefficient τ*(u:ℝ)^6 ≤
      mixedPrimeSmooth (roughParameter τ u) α (u^6) := by
  have hlog : 0 < Real.log (fastRoot u) := Real.log_pos (by exact_mod_cast hZ2)
  have ht : 0 < roughParameter τ u := div_pos hτ hlog
  have he : roughParameter τ u*Real.log (fastRoot u) = τ :=
    div_mul_cancel₀ τ hlog.ne'
  have hs := mixed_lower_from_rough hα.le ht (show 1 < fastRoot u from hZ2)
    (by rw [he]; exact hτsmall)
    (K := 49153) (N := u^6)
    (fun p hp => fast_floor_output_power_bound hαZ hZ2 (mem_Ioc.mp hp).2)
  rw [he] at hs
  have hLpos : 0 < 1+Real.log (u+1:ℕ) := by
    linarith only [Real.log_natCast_nonneg (u+1)]
  have hXpos : 0 ≤ (u:ℝ)^6 := pow_nonneg (Nat.cast_nonneg u) _
  have hbase := weighted_log_lower_transfer (A := (τ/2)^49153)
    (z := Real.log (fastRoot u)) (τ := τ)
    (C := Erdos972EfficientPrimeAlmostPrime.roughConstant)
    (L := 1+Real.log (u+1:ℕ)) (X := (u:ℝ)^6)
    (Y := coprimePrimeWeight α (fastRoot u).factorial (u^6))
    (pow_nonneg (div_nonneg hτ.le (by norm_num)) _) hlog hτ
    Erdos972EfficientPrimeAlmostPrime.roughConstant_pos hLpos hXpos
    (fastRoot_log_comparison hZ2) hweight hs
  exact hbase


/-- Both bounds concern the same mixed sum, at the same scale and the
same joint parameter. The lower envelope is smaller than the error
budget, so this is not a prime-pair lower-bound theorem. -/
theorem exists_common_layer_estimates {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (B : ℕ) : ∃ u : ℕ, B < u ∧ B < layerCount u ∧
      2 ≤ fastRoot u ∧ α ≤ fastRoot u ∧
      roughLayerCoefficient*(u:ℝ)^6/(layerCount u+1)^98304 ≤
        mixedPrimeSmooth (layerParameter α u) α (u^6) ∧
      |mixedPrimeSmooth (layerParameter α u) α (u^6)-mixedPrimeMangoldt α (u^6)| ≤
        100000*(u:ℝ)^6/(layerCount u+1) := by
  let B' := max B (max 2 ⌈α⌉₊)
  obtain ⟨u, hu, hZ, hJ, hmoment, hweight⟩ := exists_common_rough_moment_scale hα hI B'
  have hZ2 : 2 ≤ fastRoot u :=
    (le_max_left 2 _).trans ((le_max_right B _).trans hZ.le)
  have hαZ : α ≤ fastRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right 2 _).trans ((le_max_right B _).trans hZ.le)))
  have hJ1 : 1 ≤ layerCount u :=
    (show 1 ≤ 2 by decide).trans
      ((le_max_left 2 _).trans ((le_max_right B _).trans hJ.le))
  have ht := layerTau_admissible hα.le hZ2 hJ1
  have hs := rough_weight_to_smooth hα hZ2 hαZ hweight ht.1 ht.2
  rw [roughParameter_layerTau hZ2] at hs
  refine ⟨u, (le_max_left _ _).trans_lt hu, (le_max_left _ _).trans_lt hJ,
    hZ2, hαZ, ?_, layerParameter_mixed_error hα.le hmoment⟩
  have hl := mul_le_mul_of_nonneg_right (layer_coefficient_bounds hα.le hZ2 hαZ).1
    (pow_nonneg (Nat.cast_nonneg u) 6)
  apply le_trans _ hs
  simpa only [div_mul_eq_mul_div] using hl

#print axioms exists_common_rough_moment_scale
#print axioms rough_weight_to_smooth
#print axioms exists_common_layer_estimates

end Erdos972CommonRoughMomentScale
