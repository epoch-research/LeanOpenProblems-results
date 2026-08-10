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

open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma

set_option maxHeartbeats 600000

/--
Conjecture from OEIS A296075, by Robert Israel:
Are 1 and 12 the only solutions to a(n)=1?
-/
private lemma sigma_counterexample :
    ArithmeticFunction.sigma 1 ((2^14 * 4409) * 458009) = 66183576284700 := by
  have hp2 : Nat.Prime 2 := by norm_num
  have hp4409 : Nat.Prime 4409 := by norm_num
  have hp458009 : Nat.Prime 458009 := by norm_num
  have h2 : ArithmeticFunction.sigma 1 (2^14) = 32767 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp2]
    norm_num
  have h2num : ArithmeticFunction.sigma 1 16384 = 32767 := by simpa using h2
  have h4409 : ArithmeticFunction.sigma 1 4409 = 4410 := by
    rw [show 4409 = 4409^1 by norm_num, ArithmeticFunction.sigma_one_apply_prime_pow hp4409]
    norm_num
  have h458009 : ArithmeticFunction.sigma 1 458009 = 458010 := by
    rw [show 458009 = 458009^1 by norm_num, ArithmeticFunction.sigma_one_apply_prime_pow hp458009]
    norm_num
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    (show Nat.Coprime (2^14 * 4409) 458009 by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    (show Nat.Coprime (2^14) 4409 by norm_num)]
  norm_num [h2num, h4409, h458009]

private lemma zeta_sigma_counterexample :
    (ArithmeticFunction.zeta * ArithmeticFunction.sigma 1) ((2^14 * 4409) * 458009) =
      132367152569399 := by
  let F : ArithmeticFunction ℕ := ArithmeticFunction.zeta * ArithmeticFunction.sigma 1
  have hp2 : Nat.Prime 2 := by norm_num
  have hp4409 : Nat.Prime 4409 := by norm_num
  have hp458009 : Nat.Prime 458009 := by norm_num
  have hmult : ArithmeticFunction.IsMultiplicative F :=
    ArithmeticFunction.isMultiplicative_zeta.mul ArithmeticFunction.isMultiplicative_sigma
  have h2 : (ArithmeticFunction.zeta * ArithmeticFunction.sigma 1) (2^14) = 65519 := by
    rw [ArithmeticFunction.zeta_mul_apply]
    rw [Nat.sum_divisors_prime_pow hp2]
    simp only [ArithmeticFunction.sigma_one_apply_prime_pow hp2]
    norm_num
  have h2num : F 16384 = 65519 := by simpa [F] using h2
  have h4409 : F 4409 = 4411 := by
    change (ArithmeticFunction.zeta * ArithmeticFunction.sigma 1) 4409 = 4411
    rw [show 4409 = 4409^1 by norm_num]
    rw [ArithmeticFunction.zeta_mul_apply]
    rw [Nat.sum_divisors_prime_pow hp4409]
    simp only [ArithmeticFunction.sigma_one_apply_prime_pow hp4409]
    norm_num
  have h458009 : F 458009 = 458011 := by
    change (ArithmeticFunction.zeta * ArithmeticFunction.sigma 1) 458009 = 458011
    rw [show 458009 = 458009^1 by norm_num]
    rw [ArithmeticFunction.zeta_mul_apply]
    rw [Nat.sum_divisors_prime_pow hp458009]
    simp only [ArithmeticFunction.sigma_one_apply_prime_pow hp458009]
    norm_num
  change F ((2^14 * 4409) * 458009) = 132367152569399
  rw [hmult.map_mul_of_coprime (show Nat.Coprime (2^14 * 4409) 458009 by norm_num)]
  rw [hmult.map_mul_of_coprime (show Nat.Coprime (2^14) 4409 by norm_num)]
  norm_num [h2num, h4409, h458009]

private lemma a_counterexample : a ((2^14 * 4409) * 458009) = 1 := by
  unfold a
  rw [Finset.sum_sub_distrib]
  have hsum2 :
      (∑ x ∈ Nat.divisors ((2^14 * 4409) * 458009), (2 * x : ℤ)) =
        (2 * (ArithmeticFunction.sigma 1 ((2^14 * 4409) * 458009)) : ℤ) := by
    rw [← Finset.mul_sum]
    apply congrArg (fun z : ℤ => 2 * z)
    rw [← Nat.cast_sum]
    rw [← ArithmeticFunction.sigma_one_apply]
  have hsumσ :
      (∑ x ∈ Nat.divisors ((2^14 * 4409) * 458009),
          (ArithmeticFunction.sigma 1 x : ℤ)) =
        ((ArithmeticFunction.zeta * ArithmeticFunction.sigma 1)
          ((2^14 * 4409) * 458009) : ℤ) := by
    rw [← Nat.cast_sum]
    rw [← ArithmeticFunction.zeta_mul_apply]
  rw [hsum2, hsumσ, sigma_counterexample, zeta_sigma_counterexample]
  norm_num

theorem oeis_296075_conjecture_0.disproof : ¬ (∀ n : ℕ,
  a n = 1 ↔ n = 1 ∨ n = 12) := by
  intro h
  have hn := (h ((2^14 * 4409) * 458009)).mp a_counterexample
  norm_num at hn

