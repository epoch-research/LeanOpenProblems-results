import FormalConjectures.Util.ProblemImports

open Nat

/--
A296075: Sum of deficiencies of divisors of $n$.
The deficiency of a number $d$ is $2d - \sigma_1(d)$, where $\sigma_1(d)$ is the sum of the divisors of $d$.
$$a(n) = \sum_{d|n} (2d - \sigma_1(d))$$
-/
def a (n : ℕ) : ℤ :=
  (divisors n).sum fun d =>
    -- Deficiency of d: 2*d - sigma_1(d)
    (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)

lemma a_eq_two_sigma_sub_zeta_sigma (n : ℕ) :
    a n = (2 * (ArithmeticFunction.sigma 1 n : ℤ)) -
      ((ArithmeticFunction.zeta * ArithmeticFunction.sigma 1) n : ℤ) := by
  rw [a, ArithmeticFunction.zeta_mul_apply, ArithmeticFunction.sigma_one_apply]
  simp only [Finset.sum_sub_distrib]
  congr 1
  · rw [show ((↑(∑ d ∈ n.divisors, d) : ℤ)) = ∑ d ∈ n.divisors, (d : ℤ) by simp]
    rw [Finset.mul_sum]
  · simp

lemma oeis_296075_counterexample_value : a (2^14 * 4409 * 458009) = 1 := by
  have hsigma : (ArithmeticFunction.sigma 1) (2^14 * 4409 * 458009) =
      32767 * 4410 * 458010 := by
    have hmult : (ArithmeticFunction.sigma 1).IsMultiplicative :=
      ArithmeticFunction.isMultiplicative_sigma
    rw [hmult.map_mul_of_coprime]
    · rw [hmult.map_mul_of_coprime]
      · have hp2 : Nat.Prime 2 := by norm_num
        have hp1 : Nat.Prime 4409 := by norm_num
        have hpq : Nat.Prime 458009 := by norm_num
        rw [ArithmeticFunction.sigma_one_apply_prime_pow hp2]
        rw [show 4409 = 4409^1 by norm_num,
          ArithmeticFunction.sigma_one_apply_prime_pow hp1]
        rw [show 458009 = 458009^1 by norm_num,
          ArithmeticFunction.sigma_one_apply_prime_pow hpq]
        norm_num
      · norm_num
    · norm_num
  have hD : (ArithmeticFunction.zeta * ArithmeticFunction.sigma 1)
        (2^14 * 4409 * 458009) = 65519 * 4411 * 458011 := by
    have hmult : (ArithmeticFunction.zeta * ArithmeticFunction.sigma 1).IsMultiplicative :=
      ArithmeticFunction.IsMultiplicative.mul ArithmeticFunction.isMultiplicative_zeta
        ArithmeticFunction.isMultiplicative_sigma
    rw [hmult.map_mul_of_coprime]
    · rw [hmult.map_mul_of_coprime]
      · have hp2 : Nat.Prime 2 := by norm_num
        have hp1 : Nat.Prime 4409 := by norm_num
        have hpq : Nat.Prime 458009 := by norm_num
        rw [ArithmeticFunction.zeta_mul_apply, Nat.divisors_prime_pow hp2]
        rw [show 4409 = 4409^1 by norm_num]
        rw [ArithmeticFunction.zeta_mul_apply, Nat.divisors_prime_pow hp1]
        rw [show 458009 = 458009^1 by norm_num]
        rw [ArithmeticFunction.zeta_mul_apply, Nat.divisors_prime_pow hpq]
        norm_num [ArithmeticFunction.sigma_one_apply_prime_pow hp2,
          ArithmeticFunction.sigma_one_apply_prime_pow hp1,
          ArithmeticFunction.sigma_one_apply_prime_pow hpq]
      · norm_num
    · norm_num
  rw [a_eq_two_sigma_sub_zeta_sigma, hsigma, hD]
  norm_num

/--
Conjecture from OEIS A296075, by Robert Israel:
Are 1 and 12 the only solutions to a(n)=1?
-/

theorem oeis_296075_conjecture_0.disproof : ¬ (∀ n : ℕ,
  a n = 1 ↔ n = 1 ∨ n = 12) := by
  intro h
  have ha : a (2^14 * 4409 * 458009) = 1 := oeis_296075_counterexample_value
  have hbad := (h (2^14 * 4409 * 458009)).mp ha
  norm_num at hbad
