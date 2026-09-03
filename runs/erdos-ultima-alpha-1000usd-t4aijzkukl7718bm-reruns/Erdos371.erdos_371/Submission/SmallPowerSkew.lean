import FormalConjecturesUtil
import Submission.NormalizedPowerBoundary

/-! A quantitative small-power regime for the absolute normalized increment.
This is not a signed cancellation estimate in the largest-prime-dominated
regime and does not settle Erdős 371. -/

namespace Erdos371SmallPowerSkew

open Finset Filter Erdos371UniformPowerSkew Erdos371NormalizedPowerBoundary
open Erdos371SmallPrimeAveraging Erdos371PrimeDeletionVariance Erdos371ReflectionRange
open Erdos371NormalizedAdditiveDiscrepancy (skew)
open scoped Topology
attribute [local instance] Classical.propDecidable

lemma sum_excess_le_product {ι : Type*} (fs : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ fs, 1≤f i) :
    (∑ i ∈ fs, (f i-1)) ≤ (∏ i ∈ fs, f i)-1 := by
  classical
  induction fs using Finset.induction_on with
  | empty => simp
  | @insert i fs hi ih =>
    have hi1 := hf i (mem_insert_self _ _)
    have hfs : ∀ j∈fs, 1≤f j := fun j hj => hf j (mem_insert_of_mem hj)
    have hp : 1≤∏ j∈fs, f j := by
      calc
        1 = ∏ _j∈fs, (1:ℝ) := by simp
        _ ≤ _ := prod_le_prod (fun _ _ => zero_le_one) hfs
    rw [sum_insert hi,prod_insert hi]
    have hh := ih hfs
    nlinarith [mul_nonneg (sub_nonneg.mpr hi1) (sub_nonneg.mpr hp)]

lemma powerSum_lower_count {s : ℝ} (hs : 0≤s) (n : ℕ) : omega n≤powerSum s n := by
  unfold omega powerSum
  calc
    _ = ∑ _p ∈ n.primeFactors, (1:ℝ) := by simp
    _ ≤ _ := sum_le_sum (fun p hp => Real.one_le_rpow
      (by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.one_lt.le) hs)

lemma powerSum_excess_bound {s : ℝ} (hs : 0≤s) {n : ℕ} (hn : 0<n) :
    powerSum s n-omega n≤(n:ℝ)^s-1 := by
  have hh := sum_excess_le_product n.primeFactors (fun p => (p:ℝ)^s)
    (fun p hp => Real.one_le_rpow
      (by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.one_lt.le) hs)
  have hprod : (∏ p∈n.primeFactors, (p:ℝ)^s) ≤ (n:ℝ)^s := by
    rw [Real.finset_prod_rpow _ _ (fun _ _ => Nat.cast_nonneg _) s]
    apply Real.rpow_le_rpow (by positivity) _ hs
    have hh : ((∏ p ∈ n.primeFactors, p : ℕ):ℝ) ≤ n :=
      Nat.cast_le.mpr (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n))
    simpa only [Nat.cast_prod] using hh
  simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,mul_one] at hh
  exact hh.trans (sub_le_sub_right hprod 1)

lemma powerSum_deviation_bound {s : ℝ} (hs : 0≤s) {n N : ℕ} (hn : n≤N) (M : ℝ) :
    |powerSum s n-M| ≤ |omega n-M|+(N:ℝ)^s := by
  by_cases hzero : n=0
  · subst n
    simp only [powerSum,Nat.primeFactors_zero,sum_empty,omega_zero,zero_sub]
    exact le_add_of_nonneg_right (by positivity)
  have hn0 : 0<n := Nat.pos_of_ne_zero hzero
  have hexcess : |powerSum s n-omega n| ≤ (N:ℝ)^s := by
    rw [abs_of_nonneg (sub_nonneg.mpr (powerSum_lower_count hs n))]
    have hpow : (n:ℝ)^s ≤ (N:ℝ)^s := Real.rpow_le_rpow (by positivity)
      (Nat.cast_le.mpr hn) hs
    linarith [powerSum_excess_bound hs hn0]
  calc
    _ = |(powerSum s n-omega n)+(omega n-M)| := by congr 1; ring
    _ ≤ |powerSum s n-omega n|+|omega n-M| := abs_add_le _ _
    _ ≤ _ := by linarith

lemma small_power_absolute_mean_bound {s : ℝ} (hs : 0≤s) {N : ℕ} (hN : 0<N)
    (hM : 0<primeMass (N+1)) :
    mean (fun n => |normalized s n|) N ≤
      2*((Real.sqrt (3*primeMass (N+1))+2)/primeMass (N+1))+1/N+
        2*(N:ℝ)^s/primeMass (N+1) := by
  let M := primeMass (N+1)
  have hp (n : ℕ) (hn : n<N) : |normalized s n| ≤
      (|omega n-M|+|omega (n+1)-M|+2*(N:ℝ)^s)/M := by
    have hh := skew_abs_le_deviation (powerSum_nonneg s n)
      (powerSum_nonneg s (n+1)) hM
    apply hh.trans
    apply div_le_div_of_nonneg_right _ hM.le
    have h₁ := powerSum_deviation_bound hs hn.le M
    have h₂ := powerSum_deviation_bound hs (show n+1≤N by omega) M
    linarith
  have hb : mean (fun n => |normalized s n|) N ≤
      mean (fun n => (|omega n-M|+|omega (n+1)-M|+2*(N:ℝ)^s)/M) N := by
    unfold mean
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    exact sum_le_sum (fun n hn => hp n (mem_range.mp hn))
  rw [mean_div_const,mean_add,mean_add,mean_const _ hN] at hb
  have hD := deviation_bound N
  have hD' := deviation_shift_bound N
  change mean (fun n => |omega n-M|) N ≤ Real.sqrt (3*M)+M/N at hD
  change mean (fun n => |omega (n+1)-M|) N ≤ Real.sqrt (3*M) at hD'
  calc
    _ ≤ (mean (fun n => |omega n-M|) N +
        mean (fun n => |omega (n+1)-M|) N + 2*(N:ℝ)^s)/M := hb
    _ ≤ (2*Real.sqrt (3*M)+M/N+2*(N:ℝ)^s)/M :=
      div_le_div_of_nonneg_right (by linarith) hM.le
    _ = 2*Real.sqrt (3*M)/M+1/N+2*(N:ℝ)^s/M := by dsimp [M]; field_simp
    _ ≤ _ := by
      change 2*Real.sqrt (3*M)/M+1/N+2*(N:ℝ)^s/M ≤
        2*((Real.sqrt (3*M)+2)/M)+1/N+2*(N:ℝ)^s/M
      have hpos : 0≤(4:ℝ)/M := by positivity
      have he : 2*((Real.sqrt (3*M)+2)/M) = 2*Real.sqrt (3*M)/M+4/M := by ring
      rw [he]
      linarith

lemma successor_tendsto_atTop : Tendsto (fun N : ℕ => N+1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro K
  filter_upwards [eventually_ge_atTop K] with N hN
  omega

/-- This regime is below largest-prime domination: the whole normalized
increment, not just its signed mean, tends to zero in first mean. -/
theorem small_power_absolute_mean_tendsto_zero (exponent : ℕ → ℝ)
    (hs : ∀ᶠ N in atTop, 0≤exponent N)
    (hratio : Tendsto (fun N : ℕ => (N:ℝ)^(exponent N)/primeMass (N+1)) atTop (𝓝 0)) :
    Tendsto (fun N => mean (fun n => |normalized (exponent N) n|) N) atTop (𝓝 0) := by
  have hmass := primeMass_tendsto_atTop.comp successor_tendsto_atTop
  have hu := (((root_error_tendsto_zero.comp successor_tendsto_atTop).const_mul 2).add
    tendsto_one_div_atTop_nhds_zero_nat).add (hratio.const_mul 2)
  simp only [mul_zero,add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall (fun N => mean_nonneg (fun _ => abs_nonneg _) N)
  · filter_upwards [hs,eventually_gt_atTop 0,
      hmass.eventually (eventually_gt_atTop 0)] with N hsN hN hM
    simpa only [mul_div_assoc] using small_power_absolute_mean_bound hsN hN hM

theorem small_power_signed_mean_tendsto_zero (exponent : ℕ → ℝ)
    (hs : ∀ᶠ N in atTop, 0≤exponent N)
    (hratio : Tendsto (fun N : ℕ => (N:ℝ)^(exponent N)/primeMass (N+1)) atTop (𝓝 0)) :
    Tendsto (fun N => mean (normalized (exponent N)) N) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (small_power_absolute_mean_tendsto_zero exponent hs hratio)
  · intro N
    exact abs_nonneg _
  · intro N
    change |mean (normalized (exponent N)) N| ≤ mean (fun n => |normalized (exponent N) n|) N
    unfold mean
    rw [abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)

theorem bounded_power_absolute_mean_tendsto_zero (exponent : ℕ → ℝ)
    (hs : ∀ᶠ N in atTop, 0≤exponent N) (B : ℝ)
    (hB : ∀ᶠ N : ℕ in atTop, (N:ℝ)^(exponent N)≤B) :
    Tendsto (fun N => mean (fun n => |normalized (exponent N) n|) N) atTop (𝓝 0) := by
  apply small_power_absolute_mean_tendsto_zero exponent hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((primeMass_tendsto_atTop.comp successor_tendsto_atTop).const_div_atTop B)
  · exact Eventually.of_forall (fun _ => by unfold primeMass mass; positivity)
  · filter_upwards [hB] with N hN
    exact div_le_div_of_nonneg_right hN (mass_nonneg _)

/-- In particular, powers on the scale `s_N log N = O(1)` lie in the
vanishing-absolute-mean regime. This does not identify the original signs. -/
theorem bounded_log_power_absolute_mean_tendsto_zero (exponent : ℕ → ℝ)
    (hs : ∀ᶠ N in atTop, 0≤exponent N) (B : ℝ)
    (hB : ∀ᶠ N in atTop, exponent N * Real.log N≤B) :
    Tendsto (fun N => mean (fun n => |normalized (exponent N) n|) N) atTop (𝓝 0) := by
  apply bounded_power_absolute_mean_tendsto_zero exponent hs (Real.exp B)
  filter_upwards [hB,eventually_gt_atTop 0] with N hN hNpos
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hNpos)]
  exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hN)

/-- The small-power regime cannot simultaneously supply the mean-absolute
sign approximation needed to transfer its cancellation to Erdős 371. -/
theorem small_power_not_sign_approximation (exponent : ℕ → ℝ)
    (hs : ∀ᶠ N in atTop, 0≤exponent N)
    (hratio : Tendsto (fun N : ℕ => (N:ℝ)^(exponent N)/primeMass (N+1)) atTop (𝓝 0)) :
    ¬ Tendsto (fun N => mean (error (exponent N)) N) atTop (𝓝 0) := by
  intro h
  have ht := (small_power_absolute_mean_tendsto_zero exponent hs hratio).add h
  simp only [add_zero] at ht
  have hb : ∀ᶠ N in atTop,
      1 ≤ mean (fun n => |normalized (exponent N) n|) N+mean (error (exponent N)) N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [← mean_add,← mean_const 1 hN]
    apply mean_mono
    intro n
    have hsign : |(Erdos371PrimeDiscrepancy.sign n:ℝ)|=1 := by
      unfold Erdos371PrimeDiscrepancy.sign
      split_ifs <;> norm_num
    have hh := abs_sub_abs_le_abs_sub (Erdos371PrimeDiscrepancy.sign n:ℝ)
      (normalized (exponent N) n)
    rw [hsign] at hh
    change 1≤|normalized (exponent N) n|+
      |(Erdos371PrimeDiscrepancy.sign n:ℝ)-normalized (exponent N) n|
    linarith
  obtain ⟨N,hN,hsmall⟩ := (hb.and (ht.eventually_lt_const (show (0:ℝ)<1/2 by norm_num))).exists
  linarith

end Erdos371SmallPowerSkew

#print axioms Erdos371SmallPowerSkew.small_power_absolute_mean_bound

#print axioms Erdos371SmallPowerSkew.small_power_absolute_mean_tendsto_zero
#print axioms Erdos371SmallPowerSkew.small_power_signed_mean_tendsto_zero
#print axioms Erdos371SmallPowerSkew.bounded_log_power_absolute_mean_tendsto_zero
#print axioms Erdos371SmallPowerSkew.small_power_not_sign_approximation
