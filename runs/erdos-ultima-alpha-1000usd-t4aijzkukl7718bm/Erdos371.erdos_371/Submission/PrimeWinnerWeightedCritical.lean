import Submission.PrimeWinnerWeightedEnergy
import Submission.PrimeWinnerCriticalCofactor

/-! The cofactor-weighted sieve extends the critical logarithmic range
from r>2 to r>1. This does not control fixed interior prime-power bands. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma primeWinnerEnergyAbove_weighted_ratio_bound (B X z N : ℕ)
    (hN : 0 < N) (hB : 1 ≤ B) (hz : 1 ≤ z) (hzB : z ≤ B)
    (hNX : N ≤ X*(B+1)) (hNB : N ≤ (B+1)^2) :
    primeWinnerEnergyAbove B N/N ≤
      224*Real.exp 19*X*(1+Real.log X)/(Real.log (z+1 : ℝ))^2+
      28*(X : ℝ)^3*(z+1 : ℝ)^64/N+(2*X+1 : ℝ)/N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hB0 : (0 : ℝ) < B+1 := by positivity
  have hNX' : (N : ℝ)/(B+1 : ℝ) ≤ X := by
    apply (div_le_iff₀ hB0).mpr
    exact_mod_cast hNX
  have hmain := mul_le_mul_of_nonneg_left hNX'
    (show 0 ≤ 224*Real.exp 19*(1+Real.log X)/(Real.log (z+1 : ℝ))^2 by
      have := Real.log_natCast_nonneg X
      positivity)
  have herr := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hNX' 3)
    (show 0 ≤ 28*(z+1 : ℝ)^64/N by positivity)
  have hb := div_le_div_of_nonneg_right
    (primeWinnerEnergyAbove_weighted_bound B X z N hB hz hzB hNX hNB) hN0.le
  have he : (224*Real.exp 19*(N : ℝ)^2*(1+Real.log X)/
        ((B+1 : ℝ)*(Real.log (z+1 : ℝ))^2)+
      28*(N : ℝ)^3*(z+1 : ℝ)^64/(B+1 : ℝ)^3+(2*X+1 : ℝ))/N =
      (224*Real.exp 19*(1+Real.log X)/(Real.log (z+1 : ℝ))^2)*
        ((N : ℝ)/(B+1 : ℝ))+
      (28*(z+1 : ℝ)^64/N)*((N : ℝ)/(B+1 : ℝ))^3+(2*X+1 : ℝ)/N := by
    field_simp
  rw [he] at hb
  apply hb.trans
  convert add_le_add (add_le_add hmain herr) (le_refl ((2*X+1 : ℝ)/N)) using 1
  ring

noncomputable def weightedEnergyConstant : ℝ := 224*Real.exp 19*256^2

lemma primeWinnerEnergyAbove_weighted_power_sieve_ratio (B X N : ℕ)
    (hN : 1 < N) (hNX : N ≤ X*(B+1)) (hB : (N : ℝ)^(1/2 : ℝ) ≤ B) :
    primeWinnerEnergyAbove B N/N ≤
      weightedEnergyConstant*X*(1+Real.log X)/(Real.log N)^2+
      (28*(2 : ℝ)^64)*(X : ℝ)^3/(N : ℝ)^(3/4 : ℝ)+(2*X+1 : ℝ)/N := by
  let z := ⌊(N : ℝ)^(1/256 : ℝ)⌋₊
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hB1 : 1 ≤ B := by
    exact_mod_cast (Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 1/2)).trans hB
  have hz1 : 1 ≤ z := (Nat.one_le_floor_iff _).mpr
    (Real.one_le_rpow hN1 (by norm_num))
  have hzB : z ≤ B := by
    have hh := (Nat.floor_le (Real.rpow_nonneg hN0.le (1/256 : ℝ))).trans
      ((Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1/256 : ℝ) ≤ 1/2)).trans hB)
    exact_mod_cast hh
  have hNB : N ≤ (B+1)^2 := by
    have hs := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le (1/2 : ℝ)) hB 2
    have he : ((N : ℝ)^(1/2 : ℝ))^2 = N := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
      norm_num
    rw [he] at hs
    have hsq : (N : ℝ) ≤ (B+1 : ℝ)^2 := by nlinarith
    exact_mod_cast hsq
  have hzupper : (z+1 : ℝ) ≤ 2*(N : ℝ)^(1/256 : ℝ) := by
    have hz := Nat.floor_le (Real.rpow_nonneg hN0.le (1/256 : ℝ))
    have ho := Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 1/256)
    dsimp only [z]
    linarith
  have hlogz : Real.log N/256 ≤ Real.log (z+1 : ℝ) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hN0 (1/256 : ℝ))
      (Nat.lt_floor_add_one ((N : ℝ)^(1/256 : ℝ))).le
    rw [Real.log_rpow hN0] at hh
    convert hh using 1
    ring
  have hlogz0 : 0 < Real.log (z+1 : ℝ) := lt_of_lt_of_le (by positivity) hlogz
  have hsq : (Real.log N/256)^2 ≤ (Real.log (z+1 : ℝ))^2 :=
    pow_le_pow_left₀ (by positivity) hlogz 2
  have hmain := div_le_div_of_nonneg_left
    (show 0 ≤ 224*Real.exp 19*X*(1+Real.log X) by
      have := Real.log_natCast_nonneg X
      positivity) (by positivity : 0 < (Real.log N/256)^2) hsq
  have hzpow : (z+1 : ℝ)^64 ≤ (2 : ℝ)^64*(N : ℝ)^(1/4 : ℝ) := by
    calc
      _ ≤ (2*(N : ℝ)^(1/256 : ℝ))^64 := pow_le_pow_left₀ (by positivity) hzupper 64
      _ = _ := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
        norm_num
  have herr := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hzpow (show 0 ≤ 28*(X : ℝ)^3 by positivity)) hN0.le
  have hpowers : (N : ℝ)^(1/4 : ℝ)/N = 1/(N : ℝ)^(3/4 : ℝ) := by
    calc
      _ = (N : ℝ)^(1/4 : ℝ)/(N : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ)^(-(3/4 : ℝ)) := by rw [← Real.rpow_sub hN0]; norm_num
      _ = _ := by rw [Real.rpow_neg hN0.le,one_div]
  have hb := primeWinnerEnergyAbove_weighted_ratio_bound B X z N (by omega) hB1 hz1 hzB hNX hNB
  apply hb.trans
  have hm : 224*Real.exp 19*X*(1+Real.log X)/(Real.log (z+1 : ℝ))^2 ≤
      weightedEnergyConstant*X*(1+Real.log X)/(Real.log N)^2 := by
    apply hmain.trans_eq
    unfold weightedEnergyConstant
    ring
  have he : 28*(X : ℝ)^3*(z+1 : ℝ)^64/N ≤
      (28*(2 : ℝ)^64)*(X : ℝ)^3/(N : ℝ)^(3/4 : ℝ) := by
    apply herr.trans_eq
    calc
      _ = (28*(2 : ℝ)^64)*(X : ℝ)^3*((N : ℝ)^(1/4 : ℝ)/N) := by ring
      _ = _ := by rw [hpowers]; ring
  exact add_le_add (add_le_add hm he) le_rfl

lemma criticalCofactor_weighted_main_bound (r : ℝ) (N : ℕ)
    (hL : 1 ≤ Real.log N) (hK : 0 < criticalCofactorCutoff r N)
    (hK2 : criticalCofactorCutoff r N ≤ logPowerCofactorCutoff 2 N) :
    (criticalCofactorCutoff r N : ℝ)*(1+Real.log (criticalCofactorCutoff r N))/(Real.log N)^2 ≤
      2/(1+Real.log (Real.log N))^(r-1) := by
  let K := criticalCofactorCutoff r N
  let W := criticalCofactorWeight r N
  have hL0 : 0 < Real.log N := by linarith
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have ht0 := Real.log_nonneg hL
  have hb0 : 0 < 1+Real.log (Real.log N) := by positivity
  have hW0 : 0 ≤ W := by dsimp [W,criticalCofactorWeight]; positivity
  have hKW : (K : ℝ) ≤ W := Nat.floor_le hW0
  have hKpow : (K : ℝ) ≤ (Real.log N)^2 := by
    have hh := (Nat.cast_le (α := ℝ)).mpr hK2
    exact hh.trans (by
      simpa only [logPowerCofactorCutoff,Real.rpow_two] using
        (Nat.floor_le (Real.rpow_nonneg hL0.le (2 : ℝ))))
  have hlog : Real.log K ≤ 2*Real.log (Real.log N) := by
    have hh := Real.log_le_log hK0 hKpow
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hm := mul_le_mul hKW (show 1+Real.log K ≤ 2*(1+Real.log (Real.log N)) by linarith)
    (show 0 ≤ 1+Real.log K by have := Real.log_natCast_nonneg K; positivity) hW0
  apply (div_le_div_of_nonneg_right hm (sq_nonneg (Real.log N))).trans_eq
  dsimp only [W,criticalCofactorWeight]
  rw [Real.rpow_sub hb0,Real.rpow_one]
  field_simp

/-- Improved critical range: the denominator exponent need only exceed one,
not two. The proof uses the weighted sieve and the halving recurrence. -/
theorem primeWinnerEnergyAbove_weighted_critical_tendsto (r : ℝ) (hr : 1 < r) :
    Tendsto (fun N : ℕ =>
      primeWinnerEnergyAbove (N/criticalCofactorCutoff r N) N/N) atTop (nhds 0) := by
  have hr0 : 0 ≤ r := by linarith
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLL : Tendsto (fun N : ℕ => 1+Real.log (Real.log N)) atTop atTop :=
    tendsto_const_nhds.add_atTop (Real.tendsto_log_atTop.comp hL)
  have hmain := (tendsto_const_nhds.div_atTop
    ((tendsto_rpow_atTop (by linarith : 0 < r-1)).comp hLL) :
      Tendsto (fun N : ℕ => 2/(1+Real.log (Real.log N))^(r-1)) atTop (nhds 0)).const_mul
        weightedEnergyConstant
  have herr := (log_nat_pow_div_rpow_tendsto_zero 6 (3/4) (by norm_num)).const_mul
    (28*(2 : ℝ)^64)
  have hend : Tendsto (fun N : ℕ => 3*(Real.log N)^2/N) atTop (nhds 0) := by
    simpa only [Real.rpow_one,mul_div_assoc,mul_zero] using
      (log_nat_pow_div_rpow_tendsto_zero 2 1 (by norm_num)).const_mul 3
  have ht := (hmain.add herr).add hend
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => by
    unfold primeWinnerEnergyAbove; positivity)) _ ht
  filter_upwards [criticalCofactor_data r hr0,logPowerCofactor_cutoff_data 2 (by norm_num),
    eventually_gt_atTop (1 : ℕ)] with N hd hpow hN
  obtain ⟨hLN,hwlow,hwup,hK0,hKK⟩ := hd
  obtain ⟨_,_,_,hu,hcut⟩ := hpow
  let K := criticalCofactorCutoff r N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 < Real.log N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hKle : (K : ℝ) ≤ (Real.log N)^2 :=
    (Nat.floor_le (by linarith : 0 ≤ criticalCofactorWeight r N)).trans hwup
  have hB : (N : ℝ)^(1/2 : ℝ) ≤ ((N/K : ℕ) : ℝ) := by
    apply (Real.rpow_le_rpow_of_exponent_le hN1
      (show (1/2 : ℝ) ≤ 1-logPowerCofactorExponent 2 N by linarith)).trans
    exact hcut.trans (by exact_mod_cast Nat.div_le_div_left hKK hK0)
  have hsize : N ≤ K*(N/K+1) := by
    have hh := Nat.mod_lt N hK0
    have he := Nat.mod_add_div N K
    nlinarith
  have hb := primeWinnerEnergyAbove_weighted_power_sieve_ratio (N/K) K N hN hsize hB
  have hm := mul_le_mul_of_nonneg_left (criticalCofactor_weighted_main_bound r N hLN hK0 hKK)
    (show 0 ≤ weightedEnergyConstant by unfold weightedEnergyConstant; positivity)
  have hKcube : (K : ℝ)^3 ≤ (Real.log N)^6 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg K) hKle 3
    simpa only [← pow_mul] using hh
  have he := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hKcube (Real.rpow_nonneg hN0.le (3/4 : ℝ)))
    (show 0 ≤ 28*(2 : ℝ)^64 by positivity)
  have hc : (2*K+1 : ℝ) ≤ 3*(Real.log N)^2 := by
    have hLsq : 1 ≤ (Real.log N)^2 := by nlinarith
    linarith
  have he' := div_le_div_of_nonneg_right hc hN0.le
  apply hb.trans
  convert add_le_add (add_le_add hm he) he' using 1
  ring

#print axioms primeWinnerEnergyAbove_weighted_power_sieve_ratio
#print axioms criticalCofactor_weighted_main_bound
#print axioms primeWinnerEnergyAbove_weighted_critical_tendsto
end Erdos371
