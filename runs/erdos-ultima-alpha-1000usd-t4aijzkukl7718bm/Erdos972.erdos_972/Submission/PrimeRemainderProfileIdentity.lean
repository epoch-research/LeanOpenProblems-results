import Submission.CommonPrimeOffDiagonal

/-! Exact large-prime invariance of the Vaughan divisor coefficient, with
the unit correction retained. Expanding the prime-restricted remainder by
this invariance reintroduces a prime term; it does not prove decorrelation. -/
namespace Erdos972PrimeRemainderProfileIdentity

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972Vaughan Erdos972DoubleVaughan Erdos972TypeIPolynomial
open Erdos972DivisorCovariance Erdos972MellinDivisorCoefficient
open Erdos972PrimeFactorRemainder Erdos972FourFactorDiagonalSplit
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
set_option maxHeartbeats 1000000

lemma truncated_moebius_prime_invariant {U p : ℕ} (hp : p.Prime) (hUp : U < p) (n : ℕ) :
    (cutoff (μ : ArithmeticFunction ℝ) U*ζ) (n*p) =
      (cutoff (μ : ArithmeticFunction ℝ) U*ζ) n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.coe_mul_zeta_apply]
  simp only [cutoff_apply]
  rw [truncated_divisor_sum U (n*p) _ (Nat.mul_pos hn0 hp.pos),
    truncated_divisor_sum U n _ hn0]
  unfold divisorPolynomial
  apply sum_congr rfl
  intro d hd
  have hdp : d < p := (mem_Ioc.mp hd).2.trans_lt hUp
  have hc := (Nat.coprime_of_lt_prime (mem_Ioc.mp hd).1.ne' hdp hp).symm
  simp only [hc.dvd_mul_right]

/-- The unit correction prevents extending large-prime invariance to n=1. -/
lemma divisorCoeff_mul_large_prime {U p : ℕ} (hp : p.Prime) (hUp : U < p) (n : ℕ) :
    divisorCoeff U (n*p) = divisorCoeff U n - (1 : ArithmeticFunction ℝ) n := by
  have hnp : n*p ≠ 1 := by
    intro he
    exact hp.ne_one (Nat.dvd_one.mp (he ▸ dvd_mul_left p n))
  rw [divisorCoeff_eq, divisorCoeff_eq, truncated_moebius_prime_invariant hp hUp]
  rw [ArithmeticFunction.one_apply (x := n*p), if_neg hnp]
  ring

lemma divisorCoeff_prime {U p : ℕ} (hU : 1 ≤ U) (hp : p.Prime) (hUp : U < p) :
    divisorCoeff U p = -1 := by
  have he := divisorCoeff_mul_large_prime hp hUp 1
  have h1 : divisorCoeff U 1 = 0 := tail_mul_zeta_eq_zero_of_le _ U 1 hU
  simpa only [one_mul, h1, ArithmeticFunction.one_apply, if_true, sub_self, zero_sub] using he

noncomputable def largePrimeLog (V : ℕ) : ArithmeticFunction ℝ :=
  ζ*tail primeMangoldt V

lemma largePrimeLog_eq_sum (V n : ℕ) :
    largePrimeLog V n = ∑ p ∈ n.divisors, tail primeMangoldt V p :=
  ArithmeticFunction.coe_zeta_mul_apply

lemma largePrimeLog_nonneg (V n : ℕ) : 0 ≤ largePrimeLog V n := by
  rw [largePrimeLog_eq_sum]
  apply sum_nonneg
  intro p hp
  by_cases hpV : p ≤ V
  · rw [tail_eq_zero_of_le _ hpV]
  · rw [tail_eq_of_lt _ (by omega)]
    exact primeMangoldt_nonneg p

lemma largePrimeLog_le_log (V n : ℕ) : largePrimeLog V n ≤ Real.log n := by
  rw [largePrimeLog_eq_sum, ← vonMangoldt_sum]
  apply sum_le_sum
  intro p hp
  by_cases hpV : p ≤ V
  · rw [tail_eq_zero_of_le _ hpV]
    exact vonMangoldt_nonneg
  · rw [tail_eq_of_lt _ (by omega)]
    exact primeMangoldt_le p

/-- This identity is exact for every n, including prime arguments.
The prime term is not negligible: it cancels the negative profile there. -/
theorem prime_remainder_profile_identity {U V : ℕ} (hUV : U ≤ V) (n : ℕ) :
    primeTypeIIPart U V n = divisorCoeff U n*largePrimeLog V n + tail primeMangoldt V n := by
  by_cases hn : n = 0
  · subst n
    simp [divisorCoeff]
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  unfold primeTypeIIPart
  rw [mul_comm _ (tail primeMangoldt V), ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun p m => tail primeMangoldt V p*
      (tail (μ : ArithmeticFunction ℝ) U*ζ) m)]
  change (∑ p ∈ n.divisors, tail primeMangoldt V p*divisorCoeff U (n/p)) = _
  have he (p : ℕ) (hpn : p ∈ n.divisors) :
      tail primeMangoldt V p*divisorCoeff U (n/p) =
        divisorCoeff U n*tail primeMangoldt V p +
          if p = n then tail primeMangoldt V p else 0 := by
    by_cases hp0 : tail primeMangoldt V p = 0
    · simp only [hp0, zero_mul, mul_zero, ite_self, add_zero]
    obtain ⟨hpV, hp⟩ := tail_primeMangoldt_nonzero hp0
    have hpn' := Nat.dvd_of_mem_divisors hpn
    have hc := divisorCoeff_mul_large_prime hp (hUV.trans_lt hpV) (n/p)
    rw [Nat.div_mul_cancel hpn'] at hc
    have hdiv : n/p = 1 ↔ p = n := by
      rw [Nat.div_eq_iff_eq_mul_left hp.pos hpn', one_mul, eq_comm]
    simp only [ArithmeticFunction.one_apply, hdiv] at hc
    split_ifs with hpeq
    · simp only [if_pos hpeq] at hc
      nlinarith only [congrArg (tail primeMangoldt V p * ·) hc]
    · simp only [if_neg hpeq, sub_zero] at hc
      rw [hc, mul_comm, add_zero]
  simp only [sum_congr rfl he, sum_add_distrib, ← mul_sum]
  rw [sum_ite_eq', if_pos (Nat.mem_divisors_self n hn), ← largePrimeLog_eq_sum]

noncomputable def primeRemainderProfile (U V n : ℕ) : ℝ :=
  divisorCoeff U n*largePrimeLog V n

lemma prime_remainder_profile_pair_identity {U V : ℕ} (hUV : U ≤ V) (α : ℝ) (N : ℕ) :
    pairSum α N (primeTypeIIPart U V) (primeTypeIIPart U V) =
      (∑ n ∈ Ioc 0 N, primeRemainderProfile U V n*primeRemainderProfile U V (floorMul α n)) +
      (∑ n ∈ Ioc 0 N, primeRemainderProfile U V n*tail primeMangoldt V (floorMul α n)) +
      (∑ n ∈ Ioc 0 N, tail primeMangoldt V n*primeRemainderProfile U V (floorMul α n)) +
      pairSum α N (tail primeMangoldt V) (tail primeMangoldt V) := by
  unfold pairSum primeRemainderProfile
  simp only [prime_remainder_profile_identity hUV, ← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  ring

lemma prime_pairSum_eq_primeCorrelation (α : ℝ) (N : ℕ) :
    pairSum α N primeMangoldt primeMangoldt = primeCorrelation α N := by
  classical
  unfold pairSum primeCorrelation
  rw [sum_filter]
  apply sum_congr rfl
  intro n hn
  change (if n.Prime then Λ n else 0)*(if (floorMul α n).Prime then Λ (floorMul α n) else 0) = _
  by_cases hp : n.Prime <;> by_cases hq : (floorMul α n).Prime <;>
    simp [hp, hq, vonMangoldt_apply_prime]

/-- The prime correction in the profile expansion is precisely the original
prime-pair correlation, with only a finite initial segment removed. -/
lemma tail_prime_pairSum_eq {α : ℝ} (hα : 1 ≤ α) {N V : ℕ} (hVN : V ≤ N) :
    pairSum α N (tail primeMangoldt V) (tail primeMangoldt V) =
      primeCorrelation α N - primeCorrelation α V := by
  classical
  have ht : pairSum α N (tail primeMangoldt V) (tail primeMangoldt V) =
      ∑ n ∈ Ioc V N, primeMangoldt n*primeMangoldt (floorMul α n) := by
    unfold pairSum
    have hsub : Ioc V N ⊆ Ioc 0 N := by
      intro n hn
      exact mem_Ioc.mpr ⟨(Nat.zero_le V).trans_lt (mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2⟩
    calc
      _ = ∑ n ∈ Ioc V N, tail primeMangoldt V n*tail primeMangoldt V (floorMul α n) := by
        symm
        apply sum_subset hsub
        intro n hn hnot
        have hnV : n ≤ V := by
          by_contra hh
          exact hnot (mem_Ioc.mpr ⟨by omega, (mem_Ioc.mp hn).2⟩)
        rw [tail_eq_zero_of_le _ hnV, zero_mul]
      _ = _ := by
        apply sum_congr rfl
        intro n hn
        rw [tail_eq_of_lt _ (mem_Ioc.mp hn).1,
          tail_eq_of_lt _ ((mem_Ioc.mp hn).1.trans_le (self_le_floorMul hα n))]
  have he := sum_Ioc_consecutive
    (fun n => primeMangoldt n*primeMangoldt (floorMul α n)) (Nat.zero_le V) hVN
  change pairSum α V primeMangoldt primeMangoldt + _ =
    pairSum α N primeMangoldt primeMangoldt at he
  rw [prime_pairSum_eq_primeCorrelation, prime_pairSum_eq_primeCorrelation] at he
  rw [ht]
  linarith only [he]

/-- This exact re-expansion must not be used as a decorrelation estimate:
the original prime-pair count remains explicitly on its right-hand side. -/
lemma offDiagonal_profile_identity {α : ℝ} (hα : 1 ≤ α) {U V N : ℕ}
    (hUV : U ≤ V) (hVN : V ≤ N) :
    primeFactorOffDiagonal α N U V =
      (∑ n ∈ Ioc 0 N, primeRemainderProfile U V n*primeRemainderProfile U V (floorMul α n)) +
      (∑ n ∈ Ioc 0 N, primeRemainderProfile U V n*tail primeMangoldt V (floorMul α n)) +
      (∑ n ∈ Ioc 0 N, tail primeMangoldt V n*primeRemainderProfile U V (floorMul α n)) +
      (primeCorrelation α N - primeCorrelation α V) - primeVaughanDiagonal α N U V := by
  have he := prime_remainder_profile_pair_identity hUV α N
  rw [prime_remainder_diagonal_split hα, tail_prime_pairSum_eq hα hVN] at he
  linarith only [he]

#print axioms truncated_moebius_prime_invariant
#print axioms divisorCoeff_mul_large_prime
#print axioms prime_remainder_profile_identity
#print axioms prime_remainder_profile_pair_identity
#print axioms tail_prime_pairSum_eq
#print axioms offDiagonal_profile_identity
end Erdos972PrimeRemainderProfileIdentity
