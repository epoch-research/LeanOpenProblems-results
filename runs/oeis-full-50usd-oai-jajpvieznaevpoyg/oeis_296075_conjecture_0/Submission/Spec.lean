import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 800000

open Nat
open ArithmeticFunction

/--
A296075: Sum of deficiencies of divisors of $n$.
The deficiency of a number $d$ is $2d - \sigma_1(d)$, where $\sigma_1(d)$ is the sum of the divisors of $d$.
$$a(n) = \sum_{d|n} (2d - \sigma_1(d))$$
-/
def a (n : ℕ) : ℤ :=
  (divisors n).sum fun d =>
    -- Deficiency of d: 2*d - sigma_1(d)
    (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)

private def sigsum : ArithmeticFunction ℕ := ArithmeticFunction.zeta * ArithmeticFunction.sigma 1

private lemma sigsum_apply (n : ℕ) :
    sigsum n = ∑ d ∈ divisors n, ArithmeticFunction.sigma 1 d := by
  exact ArithmeticFunction.zeta_mul_apply

private lemma sigsum_mult : sigsum.IsMultiplicative := by
  dsimp [sigsum]
  exact ArithmeticFunction.isMultiplicative_zeta.mul ArithmeticFunction.isMultiplicative_sigma

private lemma sigsum_prime_pow {p k : ℕ} (hp : p.Prime) :
    sigsum (p ^ k) = ∑ i ∈ Finset.range (k + 1), ArithmeticFunction.sigma 1 (p ^ i) := by
  rw [sigsum_apply, Nat.sum_divisors_prime_pow hp]

private lemma sigma_2_14 : ArithmeticFunction.sigma 1 (2^14) = 32767 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
  norm_num

private lemma sigma_4409_1 : ArithmeticFunction.sigma 1 (4409^1) = 4410 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4409)]
  norm_num

private lemma sigma_458009_1 : ArithmeticFunction.sigma 1 (458009^1) = 458010 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 458009)]
  norm_num

private lemma sigma_4409 : ArithmeticFunction.sigma 1 4409 = 4410 := by
  simpa using sigma_4409_1

private lemma sigma_458009 : ArithmeticFunction.sigma 1 458009 = 458010 := by
  simpa using sigma_458009_1

private lemma sigsum_2_14 : sigsum (2^14) = 65519 := by
  rw [sigsum_prime_pow (by norm_num : Nat.Prime 2)]
  norm_num [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]

private lemma sigsum_4409_1 : sigsum (4409^1) = 4411 := by
  rw [sigsum_prime_pow (by norm_num : Nat.Prime 4409)]
  norm_num [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4409)]

private lemma sigsum_458009_1 : sigsum (458009^1) = 458011 := by
  rw [sigsum_prime_pow (by norm_num : Nat.Prime 458009)]
  norm_num [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 458009)]

private lemma sigsum_4409 : sigsum 4409 = 4411 := by
  simpa using sigsum_4409_1

private lemma sigsum_458009 : sigsum 458009 = 458011 := by
  simpa using sigsum_458009_1

private lemma sigma_counterexample :
    ArithmeticFunction.sigma 1 (2^14 * (4409 * 458009)) = 66183576284700 := by
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime]
  · rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime]
    · rw [sigma_2_14, sigma_4409, sigma_458009]
      norm_num
    · norm_num [Nat.Coprime]
  · norm_num [Nat.Coprime]

private lemma sigsum_counterexample :
    sigsum (2^14 * (4409 * 458009)) = 132367152569399 := by
  rw [sigsum_mult.map_mul_of_coprime]
  · rw [sigsum_mult.map_mul_of_coprime]
    · rw [sigsum_2_14, sigsum_4409, sigsum_458009]
      norm_num
    · norm_num [Nat.Coprime]
  · norm_num [Nat.Coprime]

private lemma a_eq_sigma_sub_sigsum (n : ℕ) :
    a n = (2 * (ArithmeticFunction.sigma 1 n : ℕ) : ℤ) - (sigsum n : ℤ) := by
  unfold a
  rw [sigsum_apply]
  rw [ArithmeticFunction.sigma_one_apply]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [← Finset.mul_sum]
    simp
  · norm_num

private lemma a_counterexample : a (2^14 * (4409 * 458009)) = 1 := by
  rw [a_eq_sigma_sub_sigsum, sigma_counterexample, sigsum_counterexample]
  norm_num

/--
The proposed conjecture is false: `2^14 * 4409 * 458009 = 33085221781504`
is another value at which `a(n) = 1`.
-/
theorem oeis_296075_conjecture_0.disproof : ¬ (∀ n : ℕ,
  a n = 1 ↔ n = 1 ∨ n = 12) := by
  intro h
  have hbad := (h (2^14 * (4409 * 458009))).mp a_counterexample
  norm_num at hbad
