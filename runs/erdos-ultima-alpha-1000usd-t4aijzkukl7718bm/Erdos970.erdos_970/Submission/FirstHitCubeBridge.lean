import Submission.FirstHitLowerCutoff
import Submission.FirstHitMainSum
import Submission.FirstHitEighthTail

/-! Between ratios three and four, the cubic normalizer estimate gives a
smaller reciprocal excess than the direct Rankin tail. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma primeNormalizer_cutoff_mono (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {N M : ℕ} (hNM : N ≤ M) : primeNormalizer P N ≤ primeNormalizer P M := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro Q hQ
    obtain ⟨hQP, hQN⟩ := (mem_smallDivisorFamily P Q N).mp hQ
    exact (mem_smallDivisorFamily P Q M).mpr ⟨hQP, hQN.trans hNM⟩
  · intro Q hQ _
    exact primeWeight_nonneg Q (fun p hp => hP p (((mem_smallDivisorFamily P Q M).mp hQ).1 hp))

lemma firstHitProfile_three_ge : (17 / 10 : ℝ) ≤ firstHitProfile 3 := by
  have hh := firstHitReciprocal_grid_bound 20 (by omega)
  norm_num [firstHitGridUpper] at hh
  change 1 / firstHitProfile 3 ≤ (1467 / 2500 : ℝ) at hh
  have hp := firstHitProfile_pos 3 (by norm_num)
  have hm := (div_le_iff₀ hp).mp hh
  linarith

lemma firstHitCutoff_reciprocal_beyond_cube (L : ℝ) (p : ℕ) (hp : p.Prime)
    (hLp : 20000 * firstHitProfileError ≤ log (p : ℝ))
    (hL : 7 * log (p : ℝ) ≤ L) :
    1 / primeNormalizer p.primesBelow (firstHitCutoff L p) ≤
      ((10001 / 10000 : ℝ) * (10 / 17)) / log (p : ℝ) := by
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hLp1 : 1 ≤ log (p : ℝ) := by linarith [firstHitProfileError_ge_one]
  have hN : p ^ 3 ≤ firstHitCutoff L p := by
    have hh : ((p ^ 3 : ℕ) : ℝ) ≤ exp ((L - log (p : ℝ)) / 2) := by
      rw [Nat.cast_pow, ← exp_log (pow_pos hpp 3), log_pow]
      apply exp_le_exp.mpr
      norm_num only [Nat.cast_ofNat]
      linarith
    exact_mod_cast hh.trans (Nat.le_ceil _)
  have hn := strict_normalizer_lower_through_cube p (p ^ 3) hp
    (by simpa using Nat.pow_le_pow_right (show 0 < p by exact hp.pos) (by omega : 1 ≤ 3)) hLp1 3 (by norm_num) le_rfl (by
      rw [Nat.cast_pow, log_pow]
      norm_num)
  change firstHitProfile 3 * log (p : ℝ) - _ - 3 ≤ _ at hn
  have hmono := primeNormalizer_cutoff_mono p.primesBelow
    (fun q hq => (Nat.mem_primesBelow.mp hq).2) hN
  have hprofile := mul_le_mul_of_nonneg_right firstHitProfile_three_ge hlog.le
  have hG : (17 / 10 : ℝ) * log (p : ℝ) - firstHitProfileError ≤
      primeNormalizer p.primesBelow (firstHitCutoff L p) := by
    unfold firstHitProfileError
    linarith
  have hK : 0 < firstHitProfileError := by linarith [firstHitProfileError_ge_one]
  have hh := (reciprocal_of_additive_profile_eleven_twentieths (17 / 10) _ _
    firstHitProfileError (by norm_num) hK hLp hG).2
  convert hh using 1 <;> ring

noncomputable def firstHitFarCut (L : ℝ) : ℕ := ⌊exp (L / 9)⌋₊
noncomputable def firstHitBridgePrimes (L : ℝ) : Finset ℕ :=
  (Ioc (firstHitFarCut L) (firstHitPrimeCut L 23)).filter Nat.Prime
noncomputable def firstHitBridgeCoeff : ℝ := (10001 / 10000 : ℝ) * (10 / 17) - 5 / 9
noncomputable def firstHitBridgeError : ℝ :=
  162 * firstHitBridgeCoeff * (WeightedMertens.boundConstant + 1)

lemma firstHitBridgeCoeff_nonneg : 0 ≤ firstHitBridgeCoeff := by norm_num [firstHitBridgeCoeff]
lemma firstHitBridgeError_nonneg : 0 ≤ firstHitBridgeError := by
  unfold firstHitBridgeError
  have := WeightedMertens.boundConstant_pos
  have := firstHitBridgeCoeff_nonneg
  positivity

lemma firstHitBridge_log_bounds (L : ℝ) (p : ℕ) (hp : p ∈ firstHitBridgePrimes L) :
    p.Prime ∧ L / 9 < log (p : ℝ) ∧ log (p : ℝ) ≤ L / 7 := by
  obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
  obtain ⟨hplo, hphi⟩ := mem_Ioc.mp hpI
  have hlo : exp (L / 9) < (p : ℝ) := Nat.lt_of_floor_lt hplo
  have hhi : (p : ℝ) ≤ exp (L / 7) := by
    have hh := (show (p : ℝ) ≤ firstHitPrimeCut L 23 by exact_mod_cast hphi).trans
      (Nat.floor_le (exp_pos (L / (2 * firstHitNode 23 + 1))).le)
    convert hh using 1 <;> norm_num [firstHitNode]
  have hhlo := log_lt_log (exp_pos _) hlo
  have hhhi := log_le_log (show (0 : ℝ) < p by exact_mod_cast hpp.pos) hhi
  rw [log_exp] at hhlo hhhi
  exact ⟨hpp, hhlo, hhhi⟩

lemma firstHitBridge_excess_le (L : ℝ) (p : ℕ) (hp : p ∈ firstHitBridgePrimes L)
    (hthreshold : 20000 * firstHitProfileError ≤ log (p : ℝ))
    (hEuler : eulerMass (p + 1).primesBelow ≤ (9 / 5 : ℝ) * log (p : ℝ)) :
    firstHitMeanExcess L p ≤ firstHitBridgeCoeff / ((p : ℝ) * log p) := by
  obtain ⟨hpp, hlo, hhi⟩ := firstHitBridge_log_bounds L p hp
  have hrec := firstHitCutoff_reciprocal_beyond_cube L p hpp hthreshold (by linarith)
  have hEinv : 5 / (9 * log (p : ℝ)) ≤ 1 / eulerMass p.primesBelow := by
    have hh := one_div_le_one_div_of_le
      (eulerMass_pos p.primesBelow (fun q hq => (Nat.mem_primesBelow.mp hq).2))
      ((eulerMass_strict_prefix_le p hpp).trans hEuler)
    convert hh using 1 <;> ring
  have hh := mul_le_mul_of_nonneg_left (sub_le_sub hrec hEinv)
    (show 0 ≤ 1 / (p : ℝ) by positivity)
  unfold firstHitMeanExcess firstHitBridgeCoeff
  convert hh using 1 <;> ring

theorem firstHit_bridge_sum_le (L : ℝ) (hL : 0 < L) (hsmall : 9 * log 2 ≤ L)
    (hthreshold : ∀ p ∈ firstHitBridgePrimes L, 20000 * firstHitProfileError ≤ log (p : ℝ))
    (hEuler : ∀ p ∈ firstHitBridgePrimes L,
      eulerMass (p + 1).primesBelow ≤ (9 / 5 : ℝ) * log (p : ℝ)) :
    (∑ p ∈ firstHitBridgePrimes L, firstHitMeanExcess L p) ≤
      1 / (15 * L) + firstHitBridgeError / L ^ 2 := by
  have hpt := sum_le_sum (fun p hp => firstHitBridge_excess_le L p hp
    (hthreshold p hp) (hEuler p hp))
  have heq : (∑ p ∈ firstHitBridgePrimes L, firstHitBridgeCoeff / ((p : ℝ) * log p)) =
      WeightedMertens.affineRatioPrimeInterval L firstHitBridgeCoeff 0
        (exp (L / 9)) (exp (L / 7)) := by
    unfold WeightedMertens.affineRatioPrimeInterval firstHitBridgePrimes
      firstHitFarCut firstHitPrimeCut
    norm_num [firstHitNode]
  rw [heq] at hpt
  have hh := (abs_le.mp (WeightedMertens.affineRatioPrimeInterval_scaled_error L
    firstHitBridgeCoeff 0 3 4 hL (by norm_num) (by norm_num) (by norm_num at *; exact hsmall))).2
  norm_num only [zero_div, sub_zero, abs_zero, zero_mul, add_zero] at hh
  norm_num only at hh
  rw [abs_of_nonneg firstHitBridgeCoeff_nonneg] at hh
  have hbudget : 2 * firstHitBridgeCoeff ≤ (1 / 15 : ℝ) := by norm_num [firstHitBridgeCoeff]
  have hb := div_le_div_of_nonneg_right hbudget hL.le
  unfold firstHitBridgeError
  linear_combination hpt + hh + hb

#print axioms firstHitCutoff_reciprocal_beyond_cube
#print axioms firstHit_bridge_sum_le
end Erdos970.FiniteSelberg
