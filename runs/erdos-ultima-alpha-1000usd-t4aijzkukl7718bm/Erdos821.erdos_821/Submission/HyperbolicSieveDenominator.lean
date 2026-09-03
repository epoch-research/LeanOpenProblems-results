import Submission.AvoidingHarmonicMoments

/-!
# A hyperbolic lower bound for the two-dimensional sieve denominator

Grouping harmonic divisor weights by their exact prime supports avoids
losing a fixed factor in the logarithmic truncation scale.
-/

open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.Sieve
open HigherDivisors
set_option maxHeartbeats 3000000

lemma pair_denominator_ge_support_harmonic (P : Finset ℕ) (z : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) (A : Finset ℕ)
    (hA : ∀ n ∈ A, 0 < n ∧ n ≤ z ∧ n.primeFactors ⊆ P) :
    (∑ n ∈ A, (tau 2 n : ℝ)/(n : ℝ)) ≤
      ∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z,
        (∏ p ∈ S, (((2 : ℝ)/p)⁻¹-1))⁻¹ := by
  let W := P.powerset.filter (fun S => (∏ p ∈ S, p) ≤ z)
  have hmap (n : ℕ) (hn : n ∈ A) : n.primeFactors ∈ W := by
    refine mem_filter.mpr ⟨mem_powerset.mpr (hA n hn).2.2, ?_⟩
    exact (Nat.le_of_dvd (hA n hn).1 (Nat.prod_primeFactors_dvd n)).trans (hA n hn).2.1
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply sum_le_sum
  intro S hS
  have hSP := mem_powerset.mp (mem_filter.mp hS).1
  have hrow := sum_exact_prime_support_tau_le 1 z S
    (A.filter (fun n => n.primeFactors = S)) (fun p hp => (hP p (hSP hp)).1) (by
      intro n hn
      obtain ⟨hnA,hnS⟩ := mem_filter.mp hn
      exact ⟨(hA n hnA).1, (hA n hnA).2.1, hnS⟩)
  apply hrow.trans
  rw [← Finset.prod_inv_distrib]
  simp only [Sieve.pair_sieve_weight_eq]
  apply Finset.prod_le_prod
  · intro p hp
    have hh := positive_prime_power_tau_sum_le 1 p 0 (hP p (hSP hp)).1
    simpa using hh
  · intro p hp
    exact two_prime_power_factor_le p (hP p (hSP hp)).2

lemma pair_denominator_ge_avoiding_harmonic (z M : ℕ) (hM : 0 < M) (h2M : 2 ∣ M) :
    avoidingHarmonicMoment 2 z M.primeFactors ≤
      ∑ S ∈ ((z+1).primesBelow \ M.primeFactors).powerset with (∏ p ∈ S, p) ≤ z,
        (∏ p ∈ S, (((2 : ℝ)/p)⁻¹-1))⁻¹ := by
  apply pair_denominator_ge_support_harmonic
  · intro p hp
    obtain ⟨hpz,hpM⟩ := mem_sdiff.mp hp
    have hpr := (Nat.mem_primesBelow.mp hpz).2
    refine ⟨hpr, ?_⟩
    have hp2 : p ≠ 2 := by
      intro he
      subst p
      exact hpM (Nat.prime_two.mem_primeFactors h2M hM.ne')
    have := hpr.two_le
    omega
  · intro n hn
    obtain ⟨hnz,hnM⟩ := mem_filter.mp hn
    obtain ⟨hn1,hnz⟩ := mem_Icc.mp hnz
    refine ⟨hn1, hnz, ?_⟩
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    refine mem_sdiff.mpr ⟨Nat.mem_primesBelow.mpr ⟨?_,hpr⟩, ?_⟩
    · have := Nat.le_of_dvd hn1 hpd
      omega
    · exact fun hpM => hnM p hpM hpd

/-- A full logarithmic-simplex lower bound, uniform in the excluded modulus. -/
theorem pair_denominator_hyperbolic_lower (z M : ℕ) (hz : 1 ≤ z)
    (hM : 0 < M) (h2M : 2 ∣ M) :
    ((M.totient : ℝ)/(M : ℝ))^2 * (Real.log (z+1 : ℝ))^2/2 ≤
      ∑ S ∈ ((z+1).primesBelow \ M.primeFactors).powerset with (∏ p ∈ S, p) ≤ z,
        (∏ p ∈ S, (((2 : ℝ)/p)⁻¹-1))⁻¹ := by
  have hlo := harmonicMoment_factorial_lower 2 z hz
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] at hlo
  have hmul := mul_le_mul_of_nonneg_left hlo (sq_nonneg ((M.totient : ℝ)/(M : ℝ)))
  have hexc := avoidingHarmonicMoment_totient_lower 1 z M hM
  have hmul' : ((M.totient : ℝ)/(M : ℝ))^2 * (Real.log (z+1 : ℝ))^2/2 ≤
      ((M.totient : ℝ)/(M : ℝ))^2*harmonicMoment 2 z := by
    simpa only [mul_div_assoc] using hmul
  exact hmul'.trans
    (hexc.trans (pair_denominator_ge_avoiding_harmonic z M hM h2M))

lemma pair_denominator_dyadic_hyperbolic (L M : ℕ) (hM : 0 < M) (h2M : 2 ∣ M) :
    (((M.totient : ℝ)/(M : ℝ))*(L : ℝ)*Real.log 2)^2/2 ≤
      ∑ S ∈ ((2^L+1).primesBelow \ M.primeFactors).powerset with (∏ p ∈ S, p) ≤ 2^L,
        (∏ p ∈ S, (((2 : ℝ)/p)⁻¹-1))⁻¹ := by
  have hh := pair_denominator_hyperbolic_lower (2^L) M (Nat.one_le_pow _ _ (by decide)) hM h2M
  have hlog : (L : ℝ)*Real.log 2 ≤ Real.log ((2^L : ℕ)+1 : ℝ) := by
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < ((2^L : ℕ) : ℝ))
      (show ((2^L : ℕ) : ℝ) ≤ ((2^L : ℕ) : ℝ)+1 by linarith)
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using hl
  have hlog0 : 0 ≤ (L : ℝ)*Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  apply le_trans ?_ hh
  have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 2)
    (sq_nonneg ((M.totient : ℝ)/(M : ℝ)))
  simpa only [mul_pow, ← mul_assoc, mul_div_assoc] using
    div_le_div_of_nonneg_right hpow (by norm_num : (0 : ℝ) ≤ 2)

end Erdos821.Sieve
