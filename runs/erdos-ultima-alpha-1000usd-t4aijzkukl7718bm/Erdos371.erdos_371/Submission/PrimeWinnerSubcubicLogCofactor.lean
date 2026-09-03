import Submission.PrimeLoserCollisionPowerSieve
import Submission.PrimeWinnerCriticalCofactor

/-! Sublinear prime-winner energy for every fixed cofactor log-power below
three. This remains a boundary result, not a bound for the full energy. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma logPowerCofactor_collision_data (a : ℝ) (ha : 0 ≤ a) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log N ∧ 0 < logPowerCofactorCutoff a N ∧
        logPowerCofactorCutoff a N ≤ N ∧
        N/(N/logPowerCofactorCutoff a N+1) ≤ logPowerCofactorCutoff a N ∧
        (N : ℝ)^(1/2 : ℝ) ≤ ((N/logPowerCofactorCutoff a N : ℕ) : ℝ) := by
  filter_upwards [logPowerCofactor_cutoff_data a ha,eventually_gt_atTop (1 : ℕ)] with N hd hN
  obtain ⟨hL,hK,hu0,hu,hcut⟩ := hd
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hB : (N : ℝ)^(1/2 : ℝ) ≤ ((N/logPowerCofactorCutoff a N : ℕ) : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : (1/2 : ℝ) ≤ 1-logPowerCofactorExponent a N)).trans hcut
  have hdiv : 1 ≤ N/logPowerCofactorCutoff a N := by
    exact_mod_cast (Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 1/2)).trans hB
  have hKN : logPowerCofactorCutoff a N ≤ N := by
    simpa only [one_mul] using (Nat.le_div_iff_mul_le hK).mp hdiv
  have hsize : N ≤ (N/logPowerCofactorCutoff a N+1)*logPowerCofactorCutoff a N := by
    have hh := Nat.mod_lt N hK
    have he := Nat.mod_add_div N (logPowerCofactorCutoff a N)
    nlinarith
  exact ⟨hL,hK,hKN,Nat.div_le_of_le_mul hsize,hB⟩

lemma logPowerCofactor_collision_main_bound (a : ℝ) (N : ℕ) (ha : 0 ≤ a)
    (hL : 1 ≤ Real.log N) (hK : 0 < logPowerCofactorCutoff a N) :
    (logPowerCofactorCutoff a N : ℝ)*(1+Real.log (logPowerCofactorCutoff a N))^75/(Real.log N)^3 ≤
      (a+1)^75*(1+Real.log (Real.log N))^75/(Real.log N)^(3-a) := by
  let K := logPowerCofactorCutoff a N
  have hL0 : 0 < Real.log N := by linarith
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hKW : (K : ℝ) ≤ (Real.log N)^a := Nat.floor_le (Real.rpow_nonneg hL0.le a)
  have hlogK : Real.log K ≤ a*Real.log (Real.log N) := by
    have hh := Real.log_le_log hK0 hKW
    rwa [Real.log_rpow hL0] at hh
  have hlogL := Real.log_nonneg hL
  have hlogK0 : 0 ≤ 1+Real.log K := by have := Real.log_natCast_nonneg K; positivity
  have hbase : 1+Real.log K ≤ (a+1)*(1+Real.log (Real.log N)) := by nlinarith
  have hpow := pow_le_pow_left₀ hlogK0 hbase 75
  rw [mul_pow] at hpow
  have hm := mul_le_mul hKW hpow (pow_nonneg hlogK0 75) (Real.rpow_nonneg hL0.le a)
  apply (div_le_div_of_nonneg_right hm (pow_nonneg hL0.le 3)).trans_eq
  rw [Real.rpow_sub hL0,show (Real.log N)^(3 : ℝ)=(Real.log N)^3 by norm_cast]
  field_simp

/-- The actual off-diagonal incidence count is o(N) throughout every fixed
subcubic logarithmic cofactor range. -/
theorem primeLoserCollisions_logPower_tendsto (a : ℝ) (ha : 0 ≤ a) (ha3 : a < 3) :
    Tendsto (fun N : ℕ => ((primeLoserCollisions (N/logPowerCofactorCutoff a N) N).card : ℝ)/N)
      atTop (nhds 0) := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmain : Tendsto (fun N : ℕ =>
      (collisionPowerConstant*(a+1)^75)*(1+Real.log (Real.log N))^75/(Real.log N)^(3-a))
      atTop (nhds 0) := by
    have hh := ((one_add_log_rpow_div_rpow_tendsto_zero 75 (3-a) (by norm_num) (by linarith)).comp hL).const_mul
      (collisionPowerConstant*(a+1)^75)
    have hp (x : ℝ) : x^(75 : ℝ)=x^75 := by norm_cast
    simpa only [hp,Function.comp_apply,mul_zero,mul_div_assoc] using hh
  have herr : Tendsto (fun N : ℕ =>
      (8*(2 : ℝ)^96)*(Real.log N)^(a*20)/(N : ℝ)^(1/2 : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero,mul_div_assoc] using
      (log_nat_rpow_div_rpow_tendsto_zero (a*20) (1/2) (by norm_num)).const_mul (8*(2 : ℝ)^96)
  have ht := hmain.add herr
  simp only [add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ ht
  filter_upwards [logPowerCofactor_collision_data a ha,eventually_gt_atTop (1 : ℕ)] with N hd hN
  obtain ⟨hLN,hK,hKN,hX,hB⟩ := hd
  have hL0 : 0 < Real.log N := by linarith
  have hC : 0 ≤ collisionPowerConstant := by unfold collisionPowerConstant collisionLogConstant; positivity
  have hmainB := mul_le_mul_of_nonneg_left
    (logPowerCofactor_collision_main_bound a N ha hLN hK) hC
  have hK20 : (logPowerCofactorCutoff a N : ℝ)^20 ≤ (Real.log N)^(a*20) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (logPowerCofactorCutoff a N))
      (Nat.floor_le (Real.rpow_nonneg hL0.le a)) 20
    apply hh.trans_eq
    rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
    norm_num
  have herrorB := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hK20 (show (0 : ℝ) ≤ 8*(2 : ℝ)^96 by positivity))
      (Real.rpow_nonneg (Nat.cast_nonneg N) (1/2 : ℝ))
  apply (primeLoserCollisions_power_sieve_ratio (N/logPowerCofactorCutoff a N) N
    (logPowerCofactorCutoff a N) hN hK hX hKN hB).trans
  convert add_le_add hmainB herrorB using 1 <;> simp only [mul_div_assoc,mul_assoc]

/-- Both-high incidence counts vanish for all fixed logarithmic powers,
without the restriction a<3 needed for their second moment. -/
lemma bothAbove_logPower_tendsto (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun N : ℕ => ((bothAboveSet (N/logPowerCofactorCutoff a N) N).card : ℝ)/N)
      atTop (nhds 0) := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun N : ℕ => 1/Real.log N) atTop (nhds 0) := tendsto_const_nhds.div_atTop hL
  have hmain := (((logPowerCofactorExponent_tendsto_zero a).add hdiv).pow 2).const_mul largePairConstant
  have herr := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop).const_mul
    ((2 : ℝ)^65)
  have ht := hmain.add herr
  simp only [add_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ ht
  filter_upwards [logPowerCofactor_cutoff_data a ha,eventually_gt_atTop (1 : ℕ)] with N hd hN
  obtain ⟨_,_,hu0,hu,hcut⟩ := hd
  have hs : bothAboveSet (N/logPowerCofactorCutoff a N) N ⊆
      bothLargePrimeSet N (logPowerCofactorExponent a N) := by
    intro n hn
    obtain ⟨hnN,hp,hq⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hnN,hcut.trans_lt (by exact_mod_cast hp),hcut.trans_lt (by exact_mod_cast hq)⟩
  have hc := div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr (card_le_card hs)) (Nat.cast_nonneg (α := ℝ) N)
  simpa only [Function.comp_apply,neg_div] using
    hc.trans (bothLargePrimeSet_ratio_bound N (logPowerCofactorExponent a N) hN hu0 hu)

/-- Improvement from cofactor log-power <2 to log-power <3. This only
controls primes above N/(log N)^a and does not settle the density conjecture. -/
theorem primeWinnerEnergyAbove_subcubic_logPower_tendsto (a : ℝ) (ha : 0 ≤ a) (ha3 : a < 3) :
    Tendsto (fun N : ℕ => primeWinnerEnergyAbove (N/logPowerCofactorCutoff a N) N/N)
      atTop (nhds 0) := by
  have ht := (((bothAbove_logPower_tendsto a ha).const_mul 2).add
    ((primeLoserCollisions_logPower_tendsto a ha ha3).const_mul 2)).add
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => (2 : ℝ)/N) atTop (nhds 0))
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero (fun _ => by unfold primeWinnerEnergyAbove; positivity) _ ht
  intro N
  have hh := div_le_div_of_nonneg_right
    (primeWinnerEnergyAbove_le_collisions (N/logPowerCofactorCutoff a N) N) (Nat.cast_nonneg (α := ℝ) N)
  convert hh using 1
  ring

#print axioms primeLoserCollisions_logPower_tendsto
#print axioms primeWinnerEnergyAbove_subcubic_logPower_tendsto
end Erdos371
