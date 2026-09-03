import Submission.WeightedPrimeSelberg
import Submission.AvoidingHarmonicMoments

/-!
# A one-root denominator with excluded coefficient primes

Grouping reciprocal integer weights by prime support gives a sharp
harmonic lower bound. Excluding primes costs only their Euler factor.
-/
open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.Sieve
open HigherDivisors
set_option maxHeartbeats 3000000

lemma one_prime_power_factor (p : ℕ) (hp : p.Prime) :
    1/(1-(p : ℝ)⁻¹)-1 = ((p : ℝ)-1)⁻¹ := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hp1 : (p : ℝ)-1 ≠ 0 := ne_of_gt (by linarith)
  field_simp [hp0,hp1]
  ring

lemma oneRootDenominator_ge_avoiding (z : ℕ) (Q : Finset ℕ) :
    avoidingHarmonicMoment 1 z Q ≤
      oneRootDenominator ((z+1).primesBelow \ Q) z := by
  let P := (z+1).primesBelow \ Q
  let W := P.powerset.filter (fun S => (∏ p ∈ S, p) ≤ z)
  let A := (Icc 1 z).filter (fun n => ∀ p ∈ Q, ¬p ∣ n)
  have hmap (n : ℕ) (hn : n ∈ A) : n.primeFactors ∈ W := by
    obtain ⟨hnI,hnQ⟩ := mem_filter.mp hn
    obtain ⟨hn1,hnz⟩ := mem_Icc.mp hnI
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_,?_⟩
    · intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hpn := Nat.dvd_of_mem_primeFactors hp
      have hle := Nat.le_of_dvd hn1 hpn
      exact mem_sdiff.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega,hpr⟩,
        fun hpQ => hnQ p hpQ hpn⟩
    · exact (Nat.le_of_dvd hn1 (Nat.prod_primeFactors_dvd n)).trans hnz
  change (∑ n ∈ A, (tau 1 n : ℝ)/(n : ℝ)) ≤
    ∑ S ∈ W, ∏ p ∈ S, ((p : ℝ)-1)⁻¹
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply sum_le_sum
  intro S hS
  have hSP := mem_powerset.mp (mem_filter.mp hS).1
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp =>
    (Nat.mem_primesBelow.mp (mem_sdiff.mp (hSP hp)).1).2
  have hh := sum_exact_prime_support_tau_le 0 z S
    (A.filter (fun n => n.primeFactors=S)) hSprime (by
      intro n hn
      obtain ⟨hnA,hnS⟩ := mem_filter.mp hn
      obtain ⟨hn1,hnz⟩ := mem_Icc.mp (mem_filter.mp hnA).1
      exact ⟨hn1,hnz,hnS⟩)
  simp only [zero_add,pow_one] at hh
  apply hh.trans_eq
  apply prod_congr rfl
  intro p hp
  exact one_prime_power_factor p (hSprime p hp)

lemma oneRootDenominator_euler_log_lower (z : ℕ) (hz : 1 ≤ z)
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    (∏ p ∈ Q, (1-(p : ℝ)⁻¹))*Real.log (z+1 : ℝ) ≤
      oneRootDenominator ((z+1).primesBelow \ Q) z := by
  have he := avoidingHarmonicMoment_euler_lower 0 z Q hQ
  simp only [zero_add,pow_one] at he
  have hh := harmonicMoment_factorial_lower 1 z hz
  norm_num only [pow_one,Nat.factorial_one,Nat.cast_one,div_one] at hh
  have hprod : 0 ≤ ∏ p ∈ Q, (1-(p : ℝ)⁻¹) := by
    apply prod_nonneg
    intro p hp
    have hpr : (1 : ℝ) ≤ p := by exact_mod_cast (hQ p hp).one_le
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hpr)
  exact (mul_le_mul_of_nonneg_left hh hprod).trans
    (he.trans (oneRootDenominator_ge_avoiding z Q))

lemma oneRootDenominator_totient_log_lower (c z : ℕ) (hc : 0 < c) (hz : 1 ≤ z) :
    ((c.totient : ℝ)/(c : ℝ))*Real.log (z+1 : ℝ) ≤
      oneRootDenominator ((z+1).primesBelow \ c.primeFactors) z := by
  have he := avoidingHarmonicMoment_totient_lower 0 z c hc
  simp only [zero_add,pow_one] at he
  have hh := harmonicMoment_factorial_lower 1 z hz
  norm_num only [pow_one,Nat.factorial_one,Nat.cast_one,div_one] at hh
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans
    (he.trans (oneRootDenominator_ge_avoiding z c.primeFactors))

lemma oneRootDenominator_odd_log_lower (z : ℕ) (hz : 1 ≤ z) :
    Real.log (z+1 : ℝ)/2 ≤ oneRootDenominator ((z+1).primesBelow \ {2}) z := by
  have hh := oneRootDenominator_euler_log_lower z hz {2} (by simp [Nat.prime_two])
  norm_num only [prod_singleton,Nat.cast_ofNat] at hh
  simpa only [div_eq_mul_inv,one_mul,mul_comm] using hh

end Erdos821.Sieve
