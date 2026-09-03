import Submission.MixedHarmonicMoments
import Submission.MixedPairSieve

/-!
# The mixed one-root/two-root denominator

Only one factor of phi(a)/a is lost. All bounds are uniform in the
positive even coefficient a.
-/

open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators
namespace Erdos821.Sieve
open HigherDivisors
set_option maxHeartbeats 3000000

lemma mixed_root_weight_eq (a p : ℕ) :
    (((pairRootMultiplicity a p : ℝ)/(p : ℝ))⁻¹-1)⁻¹ =
      (pairRootMultiplicity a p : ℝ)/((p : ℝ)-pairRootMultiplicity a p) := by
  by_cases hpa : p ∣ a
  · simp [pairRootMultiplicity,hpa,one_div]
  · simpa only [pairRootMultiplicity, if_neg hpa, Nat.cast_ofNat] using pair_sieve_weight_eq p

lemma mixed_positive_prime_power_sum_le (a p z : ℕ) (ha : 0 < a) (h2a : 2 ∣ a) (hp : p.Prime) :
    (∑ e ∈ Icc 1 z, (mixedDivisorWeight a.primeFactors (p^e) : ℝ)/(p : ℝ)^e) ≤
      (pairRootMultiplicity a p : ℝ)/((p : ℝ)-pairRootMultiplicity a p) := by
  have hP : ∀ q ∈ a.primeFactors, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  have hpP : p ∈ a.primeFactors ↔ p ∣ a := by simp [Nat.mem_primeFactors,hp,ha.ne']
  by_cases hpa : p ∣ a
  · have he (e : ℕ) : mixedDivisorWeight a.primeFactors (p^e) = tau 1 (p^e) := by
      rw [mixedDivisorWeight_prime_pow _ hP p e hp, if_pos (hpP.mpr hpa)]
      simp [tau, ArithmeticFunction.zeta_apply_ne (pow_ne_zero _ hp.ne_zero)]
    simp_rw [he]
    have hh := positive_prime_power_tau_sum_le 0 p z hp
    apply hh.trans_eq
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    simp only [zero_add, pow_one, pairRootMultiplicity, if_pos hpa, Nat.cast_one]
    have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
    field_simp [hp0, hp1]
    ring
  · have he (e : ℕ) : mixedDivisorWeight a.primeFactors (p^e) = tau 2 (p^e) := by
      rw [mixedDivisorWeight_prime_pow _ hP p e hp, if_neg (fun h => hpa (hpP.mp h)),
        tau_prime_pow 1 e p hp, Nat.choose_one_right]
    simp_rw [he]
    have hh := positive_prime_power_tau_sum_le 1 p z hp
    have hp2 : 2 < p := by
      have hn : p ≠ 2 := fun he => hpa (he ▸ h2a)
      have := hp.two_le
      omega
    simpa only [pairRootMultiplicity, if_neg hpa, Nat.cast_ofNat] using
      hh.trans (two_prime_power_factor_le p hp2)

lemma mixedPairDenominator_ge_harmonic (a z : ℕ) (ha : 0 < a) (h2a : 2 ∣ a) :
    mixedHarmonicMoment a.primeFactors z ≤ mixedPairDenominator a z (z+1).primesBelow := by
  let P := (z+1).primesBelow
  let W := P.powerset.filter (fun S => (∏ p ∈ S, p) ≤ z)
  have hmap (n : ℕ) (hn : n ∈ Icc 1 z) : n.primeFactors ∈ W := by
    obtain ⟨hn1,hnz⟩ := mem_Icc.mp hn
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_⟩
    · intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hle := Nat.le_of_dvd hn1 (Nat.dvd_of_mem_primeFactors hp)
      exact Nat.mem_primesBelow.mpr ⟨by omega,hpr⟩
    · exact (Nat.le_of_dvd hn1 (Nat.prod_primeFactors_dvd n)).trans hnz
  unfold mixedHarmonicMoment mixedPairDenominator
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply sum_le_sum
  intro S hS
  have hSP := mem_powerset.mp (mem_filter.mp hS).1
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp => (Nat.mem_primesBelow.mp (hSP hp)).2
  rw [← Finset.prod_inv_distrib]
  simp only [mixed_root_weight_eq]
  exact sum_exact_prime_support_multiplicative_le (mixedDivisorWeight a.primeFactors)
    (mixedDivisorWeight_multiplicative a.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp))
    z S ((Icc 1 z).filter (fun n => n.primeFactors = S)) hSprime (by
      intro n hn
      obtain ⟨hnI,hnS⟩ := mem_filter.mp hn
      exact ⟨(mem_Icc.mp hnI).1,(mem_Icc.mp hnI).2,hnS⟩)
    (fun p => (pairRootMultiplicity a p : ℝ)/((p : ℝ)-pairRootMultiplicity a p))
    (fun p hp => mixed_positive_prime_power_sum_le a p z ha h2a (hSprime p hp))

/-- The totient ratio occurs to the first power, not the second. -/
theorem mixedPairDenominator_hyperbolic_lower (a z : ℕ) (ha : 0 < a) (h2a : 2 ∣ a) (hz : 1 ≤ z) :
    ((a.totient : ℝ)/(a : ℝ))*(Real.log (z+1 : ℝ))^2/2 ≤
      mixedPairDenominator a z (z+1).primesBelow := by
  have hh := harmonicMoment_factorial_lower 2 z hz
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] at hh
  have he : ((a.totient : ℝ)/(a : ℝ))*(Real.log (z+1 : ℝ))^2/2 ≤
      ((a.totient : ℝ)/(a : ℝ))*harmonicMoment 2 z := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hh
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact he.trans ((mixedHarmonicMoment_totient_lower a z ha).trans
    (mixedPairDenominator_ge_harmonic a z ha h2a))

lemma mixedPairDenominator_dyadic_lower (a L : ℕ) (ha : 0 < a) (h2a : 2 ∣ a) :
    ((a.totient : ℝ)/(a : ℝ))*((L : ℝ)*Real.log 2)^2/2 ≤
      mixedPairDenominator a (2^L) (2^L+1).primesBelow := by
  have hh := mixedPairDenominator_hyperbolic_lower a (2^L) ha h2a
    (Nat.one_le_pow _ _ (by decide))
  have hl : (L : ℝ)*Real.log 2 ≤ Real.log ((2^L : ℕ)+1 : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((2^L : ℕ) : ℝ))
      (show ((2^L : ℕ) : ℝ) ≤ ((2^L : ℕ) : ℝ)+1 by linarith)
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h
  have hl0 : 0 ≤ (L : ℝ)*Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  apply le_trans ?_ hh
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 hl 2) (by positivity)) (by norm_num)

end Erdos821.Sieve
