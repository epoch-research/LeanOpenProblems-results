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

private lemma sum_sigma_eq_conv (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.sigma 1) d) =
      ((ArithmeticFunction.sigma 1) * ArithmeticFunction.zeta) n := by
  rw [ArithmeticFunction.mul_apply]
  have h := Nat.sum_divisorsAntidiagonal (n := n)
    (fun x y => (ArithmeticFunction.sigma 1) x * ArithmeticFunction.zeta y)
  rw [h]
  apply Finset.sum_congr rfl
  intro d hd
  have hpos : 0 < n / d := Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
  simp [ArithmeticFunction.zeta, hpos.ne']

private lemma a_formula (n : ℕ) :
    a n = (2 * ((ArithmeticFunction.sigma 1) n : ℤ)) -
      (((ArithmeticFunction.sigma 1) * ArithmeticFunction.zeta) n : ℤ) := by
  unfold a
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [ArithmeticFunction.sigma_one_apply]
    norm_num [Finset.mul_sum]
  · rw [← sum_sigma_eq_conv]
    norm_num

private lemma sigma_counterexample :
    (ArithmeticFunction.sigma 1) ((2^14) * 4409 * 458009) = 66183576284700 := by
  rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime ArithmeticFunction.isMultiplicative_sigma]
  · rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime ArithmeticFunction.isMultiplicative_sigma]
    · rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
      rw [show 4409 = 4409^1 by norm_num]
      rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4409)]
      rw [show 458009 = 458009^1 by norm_num]
      rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 458009)]
      norm_num
    · norm_num
  · norm_num

private lemma conv_two_pow :
    ((ArithmeticFunction.sigma 1) * ArithmeticFunction.zeta) (2^14) = 65519 := by
  rw [← sum_sigma_eq_conv]
  rw [Nat.divisors_prime_pow (by norm_num : Nat.Prime 2)]
  simp [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
  norm_num

private lemma conv_4409 :
    ((ArithmeticFunction.sigma 1) * ArithmeticFunction.zeta) 4409 = 4411 := by
  rw [← sum_sigma_eq_conv]
  rw [show 4409 = 4409^1 by norm_num]
  rw [Nat.divisors_prime_pow (by norm_num : Nat.Prime 4409)]
  simp [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4409)]
  norm_num

private lemma conv_458009 :
    ((ArithmeticFunction.sigma 1) * ArithmeticFunction.zeta) 458009 = 458011 := by
  rw [← sum_sigma_eq_conv]
  rw [show 458009 = 458009^1 by norm_num]
  rw [Nat.divisors_prime_pow (by norm_num : Nat.Prime 458009)]
  simp [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 458009)]
  norm_num

private lemma conv_counterexample :
    ((ArithmeticFunction.sigma 1) * ArithmeticFunction.zeta) ((2^14) * 4409 * 458009) =
      132367152569399 := by
  have hmult : ArithmeticFunction.IsMultiplicative
      ((ArithmeticFunction.sigma 1) * ArithmeticFunction.zeta) :=
    ArithmeticFunction.IsMultiplicative.mul ArithmeticFunction.isMultiplicative_sigma
      ArithmeticFunction.isMultiplicative_zeta
  rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime hmult]
  · rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime hmult]
    · rw [conv_two_pow, conv_4409, conv_458009]
      norm_num
    · norm_num
  · norm_num

/--
Conjecture from OEIS A296075, by Robert Israel:
Are 1 and 12 the only solutions to a(n)=1?
-/
theorem oeis_296075_conjecture_0.disproof : ¬ (∀ n : ℕ,
  a n = 1 ↔ n = 1 ∨ n = 12) := by
  intro h
  let N : ℕ := (2^14) * 4409 * 458009
  have ha : a N = 1 := by
    change a ((2^14) * 4409 * 458009) = 1
    rw [a_formula, sigma_counterexample, conv_counterexample]
    norm_num
  have hN : ¬ (N = 1 ∨ N = 12) := by
    norm_num [N]
  exact hN ((h N).mp ha)
