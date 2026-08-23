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

/--
Conjecture from OEIS A296075, by Robert Israel:
Are 1 and 12 the only solutions to a(n)=1?
-/
private lemma a_eq_sigma (n : ℕ) :
    a n = (2 * (ArithmeticFunction.sigma 1 n) : ℤ) -
      ((ArithmeticFunction.zeta * ArithmeticFunction.sigma 1) n : ℤ) := by
  unfold a
  rw [ArithmeticFunction.zeta_mul_apply, ArithmeticFunction.sigma_one_apply]
  push_cast
  rw [Finset.sum_sub_distrib]
  simp [Finset.mul_sum]

/-- The proposed characterization is false at `33085221781504`. -/
theorem oeis_296075_conjecture_0.disproof : ¬ (∀ n : ℕ,
    a n = 1 ↔ n = 1 ∨ n = 12) := by
  intro h
  have hsigma :
      ArithmeticFunction.sigma 1 33085221781504 = 66183576284700 := by
    rw [show 33085221781504 = (2 ^ 14 * 4409) * 458009 by norm_num]
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    have h₁ : ArithmeticFunction.sigma 1 4409 = 4410 := by
      rw [show 4409 = 4409 ^ 1 by norm_num]
      rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4409)]
      norm_num [Finset.sum_range_succ]
    have h₂ : ArithmeticFunction.sigma 1 458009 = 458010 := by
      rw [show 458009 = 458009 ^ 1 by norm_num]
      rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 458009)]
      norm_num [Finset.sum_range_succ]
    rw [h₁, h₂]
    norm_num [Finset.sum_range_succ]
  have hsum :
      (ArithmeticFunction.zeta * ArithmeticFunction.sigma 1) 33085221781504 =
        132367152569399 := by
    let F := ArithmeticFunction.zeta * ArithmeticFunction.sigma 1
    have hF : F.IsMultiplicative :=
      ArithmeticFunction.isMultiplicative_zeta.mul
        ArithmeticFunction.isMultiplicative_sigma
    change F 33085221781504 = _
    rw [show 33085221781504 = (2 ^ 14 * 4409) * 458009 by norm_num]
    rw [hF.map_mul_of_coprime (by norm_num)]
    rw [hF.map_mul_of_coprime (by norm_num)]
    have hb (p e : ℕ) (hp : p.Prime) :
        (ArithmeticFunction.zeta * ArithmeticFunction.sigma 1) (p ^ e) =
          ∑ j ∈ Finset.range (e + 1), ∑ k ∈ Finset.range (j + 1), p ^ k := by
      rw [ArithmeticFunction.zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
      apply Finset.sum_congr rfl
      intro j hj
      exact ArithmeticFunction.sigma_one_apply_prime_pow hp
    change
      (ArithmeticFunction.zeta * ArithmeticFunction.sigma 1) (2 ^ 14) *
        (ArithmeticFunction.zeta * ArithmeticFunction.sigma 1) 4409 *
        (ArithmeticFunction.zeta * ArithmeticFunction.sigma 1) 458009 = _
    rw [hb 2 14 (by norm_num)]
    rw [show 4409 = 4409 ^ 1 by norm_num, hb 4409 1 (by norm_num)]
    rw [show 458009 = 458009 ^ 1 by norm_num, hb 458009 1 (by norm_num)]
    norm_num [Finset.sum_range_succ]
  have ha : a 33085221781504 = 1 := by
    rw [a_eq_sigma, hsigma, hsum]
    norm_num
  have := (h 33085221781504).mp ha
  norm_num at this
