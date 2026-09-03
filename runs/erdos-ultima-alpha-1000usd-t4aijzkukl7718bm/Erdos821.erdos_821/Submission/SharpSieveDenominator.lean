import Submission.SharpPairSieve

/-!
# A sharper elementary prime-logarithm budget for the sieve

The factorial identity gives sum_{p<=N} log(p)/p <= log(N)+log(4).
This permits a shorter truncation of the two-dimensional Euler product.
-/

open Finset Filter
open scoped Classical BigOperators

namespace Erdos821.Sieve

set_option maxHeartbeats 3000000

lemma div_le_factorization_factorial (N p : ℕ) (hp : p.Prime) :
    N/p ≤ N.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (show Nat.log p N < Nat.log p N + 2 by omega)]
  have h : 1 ∈ Finset.Ico 1 (Nat.log p N + 2) := by simp
  simpa only [pow_one] using
    (Finset.single_le_sum (fun i _ => Nat.zero_le (N/p^i)) h)

lemma sum_prime_log_div_le_log_add (N : ℕ) (hN : 0 < N) :
    (∑ p ∈ (N+1).primesBelow, Real.log ((p : ℕ) : ℝ)/((p : ℕ) : ℝ)) ≤
      Real.log (N : ℝ)+Real.log 4 := by
  let P := (N+1).primesBelow
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p ≤ N := by
    obtain ⟨hpN,hpr⟩ := Nat.mem_primesBelow.mp hp
    exact ⟨hpr, by omega⟩
  have hpoint (p : ℕ) (hp : p ∈ P) :
      (N : ℝ)*(Real.log ((p : ℕ) : ℝ)/((p : ℕ) : ℝ)) ≤
        (N.factorial.factorization p : ℝ)*Real.log p + Real.log p := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
    have hdiv : (N : ℝ)/(p : ℝ) ≤ (N/p : ℕ)+1 := by
      apply (div_le_iff₀ hp0).mpr
      have hn := (Nat.lt_mul_div_succ N (hP p hp).1.pos).le
      exact_mod_cast (by simpa only [Nat.mul_comm] using hn)
    have hv : (N/p : ℕ) ≤ N.factorial.factorization p :=
      div_le_factorization_factorial N p (hP p hp).1
    have hvR : ((N/p : ℕ) : ℝ) ≤ N.factorial.factorization p := by exact_mod_cast hv
    have hl := Real.log_natCast_nonneg p
    have hh := mul_le_mul_of_nonneg_right (hdiv.trans (add_le_add hvR le_rfl)) hl
    convert hh using 1 <;> ring
  have hsub : P ⊆ N.factorial.primeFactors := by
    intro p hp
    exact (hP p hp).1.mem_primeFactors ((hP p hp).1.dvd_factorial.mpr (hP p hp).2)
      (Nat.factorial_ne_zero N)
  have hvsum : (∑ p ∈ P, (N.factorial.factorization p : ℝ)*Real.log p) ≤
      Real.log (N.factorial : ℝ) := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
  have hfact : Real.log (N.factorial : ℝ) ≤ (N : ℝ)*Real.log N := by
    have hh := Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
      (show (N.factorial : ℝ) ≤ (N : ℝ)^N by exact_mod_cast Nat.factorial_le_pow N)
    simpa only [Real.log_pow] using hh
  have htheta : (∑ p ∈ P, Real.log (p : ℝ)) ≤ Real.log 4*(N : ℝ) := by
    rw [← theta_nat_eq_sum_primesBelow]
    exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < N by exact_mod_cast hN)).mp
  have hsum := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  nlinarith only [hsum, hvsum, hfact, htheta]

lemma sum_prime_log_div_dyadic_sharp (L : ℕ) :
    (∑ p ∈ (2^L+1 : ℕ).primesBelow, Real.log ((p : ℕ) : ℝ)/((p : ℕ) : ℝ)) ≤
      ((L : ℝ)+2)*Real.log 2 := by
  have hh := sum_prime_log_div_le_log_add (2^L) (by positivity)
  have hlog4 : Real.log 4 = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, hlog4, add_mul] using hh

lemma pair_sieve_denominator_ge_half_product_sharp (L : ℕ) (hL : 4 ≤ L)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2 < p ∧ p ≤ 2 ^ L) :
    (∏ p ∈ P, (p : ℝ) / ((p : ℝ) - 2)) / 2 ≤
      ∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ 2 ^ (6 * L),
        (∏ p ∈ S, (((2 : ℝ) / p)⁻¹ - 1))⁻¹ := by
  let w : ℕ → ℝ := fun p => 2 / ((p : ℝ) - 2)
  have hpR (p : ℕ) (hp : p ∈ P) : (2 : ℝ) < p := by exact_mod_cast (hP p hp).2.1
  have hw (p : ℕ) (hp : p ∈ P) : 0 ≤ w p := div_nonneg (by norm_num) (by linarith [hpR p hp])
  have hquot (p : ℕ) (hp : p ∈ P) : w p / (1 + w p) = 2 / (p : ℝ) := by
    dsimp [w]
    have hden : (p : ℝ) - 2 ≠ 0 := by linarith [hpR p hp]
    have hp0 : (p : ℝ) ≠ 0 := by linarith [hpR p hp]
    field_simp [hden, hp0]
    ring
  have hfull (p : ℕ) (hp : p ∈ P) : 1 + w p = (p : ℝ) / ((p : ℝ) - 2) := by
    dsimp [w]
    have hden : (p : ℝ) - 2 ≠ 0 := by linarith [hpR p hp]
    field_simp
    ring
  have hsub : P ⊆ (2 ^ L + 1).primesBelow := by
    intro p hp
    exact Nat.mem_primesBelow.mpr ⟨by have := (hP p hp).2.2; omega, (hP p hp).1⟩
  have hsum : (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) ≤ ((L : ℝ)+2)*Real.log 2 := by
    apply le_trans ?_ (sum_prime_log_div_dyadic_sharp L)
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_lt.le))
      (Nat.cast_nonneg p)
  have hmoment : 2 * (∑ p ∈ P, w p / (1 + w p) * Real.log p) ≤
      Real.log ((2 ^ (6 * L) : ℕ) : ℝ) := by
    have heq : (∑ p ∈ P, w p / (1 + w p) * Real.log p) =
        2 * (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [hquot p hp]
      ring
    rw [heq, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    push_cast
    have hLR : (4 : ℝ) ≤ L := by exact_mod_cast hL
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  have hhalf := half_euler_product_le_truncated_of_log_moment P w
    (fun p hp => (hP p hp).1.one_lt.le) hw (2 ^ (6 * L))
    (one_lt_pow₀ (by decide) (by omega)) hmoment
  have hprod : (∏ p ∈ P, (1 + w p)) = ∏ p ∈ P, (p : ℝ) / ((p : ℝ) - 2) :=
    Finset.prod_congr rfl hfull
  rw [hprod] at hhalf
  simpa only [← Finset.prod_inv_distrib, pair_sieve_weight_eq, w] using hhalf

lemma pair_sieve_denominator_log_lower_sharp (L M : ℕ) (hL : 4 ≤ L) (hM : 0 < M)
    (h2M : 2 ∣ M) :
    let P := (2 ^ L + 1).primesBelow \ M.primeFactors
    ((Nat.totient M : ℝ) / M * (L : ℝ) * Real.log 2) ^ 2 / 2 ≤
      ∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ 2 ^ (6 * L),
        (∏ p ∈ S, (((2 : ℝ) / p)⁻¹ - 1))⁻¹ := by
  dsimp only
  let P := (2 ^ L + 1).primesBelow \ M.primeFactors
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ 2 < p ∧ p ≤ 2 ^ L := by
    obtain ⟨hpQ, hpM⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpL, hprime⟩ := Nat.mem_primesBelow.mp hpQ
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact hpM (Nat.prime_two.mem_primeFactors h2M hM.ne')
    exact ⟨hprime, by have := hprime.two_le; omega, by omega⟩
  have hratio : 0 ≤ (Nat.totient M : ℝ) / M := by positivity
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hH : ((Nat.totient M : ℝ) / M * L * Real.log 2) ≤
      (harmonic (2 ^ L) : ℝ) * ((Nat.totient M : ℝ) / M) := by
    have hlog : (L : ℝ) * Real.log 2 ≤ (harmonic (2 ^ L) : ℝ) := by
      have h := log_le_harmonic_floor (y := ((2 ^ L : ℕ) : ℝ)) (Nat.cast_nonneg _)
      rw [Nat.floor_natCast] at h
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h
    have hmul := mul_le_mul_of_nonneg_right hlog hratio
    nlinarith
  have hE := hH.trans (harmonic_mul_totient_ratio_le_euler_product (2 ^ L) M hM)
  have hsq : ((Nat.totient M : ℝ) / M * L * Real.log 2) ^ 2 ≤
      (∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹) ^ 2 := by
    exact pow_le_pow_left₀ (mul_nonneg (mul_nonneg hratio (Nat.cast_nonneg L)) hlog2) hE 2
  exact (div_le_div_of_nonneg_right
    (hsq.trans (prime_euler_product_sq_le_pair_product P (fun p hp => (hP p hp).2.1)))
      (by norm_num)).trans (pair_sieve_denominator_ge_half_product_sharp L hL P hP)


end Erdos821.Sieve
