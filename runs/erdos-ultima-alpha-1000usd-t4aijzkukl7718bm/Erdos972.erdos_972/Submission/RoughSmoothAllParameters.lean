import Submission.CommonRoughMomentScale

/-!
The exact Euler-product rough-output lower bound, without a small-parameter
restriction. Its lower envelope is below the available least-factor error
budget for every positive smoothing parameter. This is not an upper bound
on the actual smoothed sum or a lower bound on the actual error.
-/
namespace Erdos972RoughSmoothAllParameters

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972RoughSmoothLowerBound Erdos972RoughSmoothComparison
open Erdos972CommonRoughMomentScale Erdos972PrimeLeastFactorScales
open Erdos972PrimePowerError Erdos972EfficientSieveScale
open Erdos972GrowingCoprimeCandidates Erdos972LeastFactorCutoff
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972PrimeRoughOutputs Erdos972PrimeAlmostPrime

set_option maxHeartbeats 2000000
set_option exponentiation.threshold 8192

lemma exp_factor_bounds {τ : ℝ} (hτ : 0 < τ) :
    0 < 1-Real.exp (-τ) ∧ 1-Real.exp (-τ) ≤ 1 ∧ 1-Real.exp (-τ) ≤ τ := by
  have hsmall := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hτ)
  have hpos := Real.exp_pos (-τ)
  have htangent := Real.add_one_le_exp (-τ)
  exact ⟨by linarith only [hsmall], by linarith only [hpos], by linarith only [htangent]⟩

/-- The exact Euler-product factor replaces the small-parameter Taylor
lower bound. The output is still only certified to have at most K factors. -/
theorem rough_smooth_lower_exp {t : ℝ} (ht : 0 < t) {n Z K : ℕ}
    (hn : 1 < n) (hZ : 1 < Z) (hc : n.Coprime Z.factorial)
    (hK : n.primeFactorsList.length ≤ K) :
    (1-Real.exp (-(t*Real.log Z)))^K/t ≤ smoothMangoldt t n := by
  have hlog : 0 < Real.log Z := Real.log_pos (by exact_mod_cast hZ)
  have hbase := exp_factor_bounds (mul_pos ht hlog)
  have hcard : n.primeFactors.card ≤ K :=
    (List.toFinset_card_le n.primeFactorsList).trans hK
  have he : (1-Real.exp (-(t*Real.log Z)))^K ≤ expDivisorSum t n := by
    rw [expDivisorSum_product t (by omega)]
    calc
      _ ≤ (1-Real.exp (-(t*Real.log Z)))^n.primeFactors.card :=
        pow_le_pow_of_le_one hbase.1.le hbase.2.1 hcard
      _ = ∏ p ∈ n.primeFactors, (1-Real.exp (-(t*Real.log Z))) := (prod_const _).symm
      _ ≤ _ := by
        apply prod_le_prod (fun _ _ => hbase.1.le)
        intro p hp
        have hl := Real.log_le_log (Nat.cast_pos.mpr (by omega : 0 < Z))
          (Nat.cast_le.mpr (primeFactor_gt_of_coprime_factorial hc hp).le)
        have hh := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hl (by linarith : -t ≤ 0))
        simpa only [neg_mul] using sub_le_sub_left hh 1
  rw [smoothMangoldt, expDivisorSum_at_zero, one_apply, if_neg (by omega : n ≠ 1), sub_zero]
  exact div_le_div_of_nonneg_right he ht.le

lemma mixed_lower_from_rough_exp {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t)
    {N Z K : ℕ} (hZ : 1 < Z)
    (hsize : ∀ p ∈ Ioc 0 N, floorMul α p ≤ Z^K) :
    (1-Real.exp (-(t*Real.log Z)))^K/t * coprimePrimeWeight α Z.factorial N ≤
      mixedPrimeSmooth t α N := by
  classical
  rw [coprimePrimeWeight, mul_sum]
  calc
    _ ≤ ∑ p ∈ (Ioc 0 N).filter
        (fun p => p.Prime ∧ (floorMul α p).Coprime Z.factorial),
        primeWeight p*smoothMangoldt t (floorMul α p) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpN, hpp, hpc⟩ := mem_filter.mp hp
      have hpout : 1 < floorMul α p := (show 1 < p from hpp.two_le).trans_le (self_le_floorMul hα p)
      have hk := factor_length_bound (by omega : 0 < floorMul α p) hZ hpc (hsize p hpN)
      have hl := rough_smooth_lower_exp ht hpout hZ hpc hk
      rw [primeWeight, if_pos hpp]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hl (Real.log_natCast_nonneg p)
    _ ≤ mixedPrimeSmooth t α N := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro p hp _
      exact mul_nonneg (primeWeight_nonneg p) (smoothMangoldt_nonneg ht _)

noncomputable def exactRoughCoefficient (τ : ℝ) : ℝ :=
  (1-Real.exp (-τ))^49153/(8195*τ*Erdos972EfficientPrimeAlmostPrime.roughConstant)

lemma exactRoughCoefficient_pos {τ : ℝ} (hτ : 0 < τ) :
    0 < exactRoughCoefficient τ :=
  div_pos (pow_pos (exp_factor_bounds hτ).1 _)
    (mul_pos (mul_pos (by norm_num) hτ) Erdos972EfficientPrimeAlmostPrime.roughConstant_pos)

/-- The lower bound is valid for every tau>0, at a fixed scale with the
already established rough-weight estimate. -/
theorem rough_weight_to_smooth_exp {α : ℝ} (hα : 1 < α) {u : ℕ}
    (hZ2 : 2 ≤ fastRoot u) (hαZ : α ≤ fastRoot u)
    (hweight : (u:ℝ)^6/(Erdos972EfficientPrimeAlmostPrime.roughConstant*
      (1+Real.log (u+1:ℕ))) ≤ coprimePrimeWeight α (fastRoot u).factorial (u^6))
    {τ : ℝ} (hτ : 0 < τ) :
    exactRoughCoefficient τ*(u:ℝ)^6 ≤
      mixedPrimeSmooth (roughParameter τ u) α (u^6) := by
  have hlog : 0 < Real.log (fastRoot u) := Real.log_pos (by exact_mod_cast hZ2)
  have ht : 0 < roughParameter τ u := div_pos hτ hlog
  have he : roughParameter τ u*Real.log (fastRoot u) = τ := div_mul_cancel₀ τ hlog.ne'
  have hs := mixed_lower_from_rough_exp hα.le ht (show 1 < fastRoot u from hZ2)
    (K := 49153) (N := u^6)
    (fun p hp => fast_floor_output_power_bound hαZ hZ2 (mem_Ioc.mp hp).2)
  rw [he] at hs
  have hLpos : 0 < 1+Real.log (u+1:ℕ) :=
    add_pos_of_pos_of_nonneg zero_lt_one (Real.log_natCast_nonneg (u+1))
  have hXpos : 0 ≤ (u:ℝ)^6 := pow_nonneg (Nat.cast_nonneg u) _
  have hbase := weighted_log_lower_transfer (A := (1-Real.exp (-τ))^49153)
    (z := Real.log (fastRoot u)) (τ := τ)
    (C := Erdos972EfficientPrimeAlmostPrime.roughConstant)
    (L := 1+Real.log (u+1:ℕ)) (X := (u:ℝ)^6)
    (Y := coprimePrimeWeight α (fastRoot u).factorial (u^6))
    (pow_nonneg (exp_factor_bounds hτ).1.le _) hlog hτ
    Erdos972EfficientPrimeAlmostPrime.roughConstant_pos hLpos hXpos
    (fastRoot_log_comparison hZ2) hweight hs
  exact hbase

lemma power_div_linear_le {b τ D : ℝ} {K : ℕ} (hτ : 0 < τ)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hbτ : b ≤ τ) (hD : 1 ≤ D) (hK : 2 ≤ K) :
    b^K/(D*τ) ≤ τ := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  apply (div_le_iff₀ (mul_pos hDpos hτ)).mpr
  have hk := pow_le_pow_of_le_one hb hb1 hK
  have ht := pow_le_pow_left₀ hb hbτ 2
  have hd := mul_le_mul_of_nonneg_right hD (sq_nonneg τ)
  nlinarith only [hk, ht, hd]

lemma exactRoughCoefficient_le {τ : ℝ} (hτ : 0 < τ) :
    exactRoughCoefficient τ ≤ τ := by
  have hC : 1 ≤ Erdos972EfficientPrimeAlmostPrime.roughConstant := by
    unfold Erdos972EfficientPrimeAlmostPrime.roughConstant
      Erdos972SelbergMajorantSize.majorantCap
    exact one_le_mul_of_one_le_of_one_le (by norm_num)
      (one_le_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)))
  have hb := exp_factor_bounds hτ
  have hd : 1 ≤ 8195*Erdos972EfficientPrimeAlmostPrime.roughConstant :=
    one_le_mul_of_one_le_of_one_le (by norm_num) hC
  have hh := power_div_linear_le (K := 49153) hτ hb.1.le hb.2.1 hb.2.2 hd (by decide)
  unfold exactRoughCoefficient
  rw [mul_right_comm (8195:ℝ) τ Erdos972EfficientPrimeAlmostPrime.roughConstant]
  exact hh

noncomputable def roughMomentError (α τ : ℝ) (u : ℕ) : ℝ :=
  roughParameter τ u*Real.log (floorMul α (u^6)) *
    (100000*(u:ℝ)^6*(layerCount u+1))

lemma error_scalar_lower {τ z L N J : ℝ} (hτ : 0 < τ) (hz : 0 < z)
    (hzL : z ≤ L) (hN : 0 < N) (hJ : 1 ≤ J) :
    τ*N < (τ/z)*L*(100000*N*J) := by
  have ht : 0 < τ/z := div_pos hτ hz
  have ha : τ ≤ (τ/z)*L := by
    calc
      τ = (τ/z)*z := (div_mul_cancel₀ τ hz.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hzL ht.le
  have hb : N < 100000*N*J := by
    have hh := mul_le_mul_of_nonneg_left hJ (show 0 ≤ 100000*N by positivity)
    nlinarith only [hh, hN]
  have hB : 0 < 100000*N*J := hN.trans hb
  exact (mul_lt_mul_of_pos_left hb hτ).trans_le
    (mul_le_mul_of_nonneg_right ha hB.le)

/-- Even the exact (non-Taylor) Euler-product lower envelope lies below
the available error budget for EVERY positive smoothing parameter. -/
theorem all_parameters_lower_envelope_lt_budget {α τ : ℝ} (hα : 1 ≤ α)
    (hτ : 0 < τ) {u : ℕ} (hZ : 2 ≤ fastRoot u) :
    exactRoughCoefficient τ*(u:ℝ)^6 < roughMomentError α τ u := by
  have hZu : fastRoot u ≤ u :=
    (root64_le_self _).trans (root64_le_self u)
  have hu : 0 < u := by omega
  have hN : (0:ℝ) < (u:ℝ)^6 := pow_pos (Nat.cast_pos.mpr hu) _
  have hz : 0 < Real.log (fastRoot u) := Real.log_pos (by exact_mod_cast hZ)
  have hn : fastRoot u ≤ floorMul α (u^6) :=
    hZu.trans ((Nat.le_pow (by decide : 0 < 6)).trans (self_le_floorMul hα _))
  have hl := Erdos972ExponentialSum.monotone_log_natCast hn
  dsimp only at hl
  have hj : (1:ℝ) ≤ layerCount u+1 := by
    linarith only [Nat.cast_nonneg (α := ℝ) (layerCount u)]
  exact (mul_le_mul_of_nonneg_right (exactRoughCoefficient_le hτ) hN.le).trans_lt
    (error_scalar_lower hτ hz hl hN hj)


lemma rough_moment_error {α τ : ℝ} (hα : 1 ≤ α) (hτ : 0 < τ)
    {u : ℕ} (hZ : 2 ≤ fastRoot u)
    (hbound : primeLeastFactorMoment α (u^6) ≤ 100000*(u:ℝ)^6*(layerCount u+1)) :
    |mixedPrimeSmooth (roughParameter τ u) α (u^6)-mixedPrimeMangoldt α (u^6)| ≤
      roughMomentError α τ u := by
  have ht : 0 < roughParameter τ u :=
    div_pos hτ (Real.log_pos (by exact_mod_cast hZ))
  apply (mixed_error_least_factor hα ht (u^6)).trans
  exact mul_le_mul_of_nonneg_left hbound
    (mul_nonneg ht.le (Real.log_natCast_nonneg (floorMul α (u^6))))

/-- One actual common scale works for ALL positive tau, with no exchange
of limits or independent scale choices. The third conjunct records why
these specific two bounds cannot certify positive prime correlation. -/
theorem exists_all_parameter_estimates {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (B : ℕ) : ∃ u : ℕ, B < u ∧ B < layerCount u ∧
      2 ≤ fastRoot u ∧ α ≤ fastRoot u ∧
      ∀ τ : ℝ, 0 < τ →
        exactRoughCoefficient τ*(u:ℝ)^6 ≤ mixedPrimeSmooth (roughParameter τ u) α (u^6) ∧
        |mixedPrimeSmooth (roughParameter τ u) α (u^6)-mixedPrimeMangoldt α (u^6)| ≤
          roughMomentError α τ u ∧
        exactRoughCoefficient τ*(u:ℝ)^6 < roughMomentError α τ u := by
  let B' := max B (max 2 ⌈α⌉₊)
  obtain ⟨u, hu, hZ, hJ, hmoment, hweight⟩ := exists_common_rough_moment_scale hα hI B'
  have hZ2 : 2 ≤ fastRoot u :=
    (le_max_left 2 _).trans ((le_max_right B _).trans hZ.le)
  have hαZ : α ≤ fastRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right 2 _).trans ((le_max_right B _).trans hZ.le)))
  refine ⟨u, (le_max_left _ _).trans_lt hu, (le_max_left _ _).trans_lt hJ,
    hZ2, hαZ, ?_⟩
  intro τ hτ
  exact ⟨rough_weight_to_smooth_exp hα hZ2 hαZ hweight hτ,
    rough_moment_error hα.le hτ hZ2 hmoment,
    all_parameters_lower_envelope_lt_budget hα.le hτ hZ2⟩

#print axioms rough_smooth_lower_exp
#print axioms rough_weight_to_smooth_exp
#print axioms all_parameters_lower_envelope_lt_budget
#print axioms exists_all_parameter_estimates

end Erdos972RoughSmoothAllParameters
