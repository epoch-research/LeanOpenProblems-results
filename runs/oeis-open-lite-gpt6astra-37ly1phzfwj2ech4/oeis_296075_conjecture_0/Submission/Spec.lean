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
theorem oeis_296075_conjecture_0 : ∀ n : ℕ,
  a n = 1 ↔ n = 1 ∨ n = 12 := by
  sorry

namespace A296075Counterexample

open ArithmeticFunction

-- The divisor sum of sigma is multiplicative.
def B : ArithmeticFunction ℕ := zeta * sigma 1

theorem a_eq (n : ℕ) : a n = 2 * (sigma 1 n : ℤ) - (B n : ℤ) := by
  rw [a, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Nat.cast_sum, ← Nat.cast_sum, ← sigma_one_apply, ← zeta_mul_apply]
  rfl

theorem B_mult : B.IsMultiplicative :=
  isMultiplicative_zeta.mul isMultiplicative_sigma

theorem B_pow (p k : ℕ) (hp : p.Prime) :
    B (p ^ k) = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (i + 1), p ^ j := by
  simp only [B, zeta_mul_apply, sum_divisors_prime_pow hp,
    sigma_one_apply_prime_pow hp]

theorem sigma_prime (p : ℕ) (hp : p.Prime) : sigma 1 p = p + 1 := by
  simpa [Finset.sum_range_succ, add_comm] using
    (sigma_one_apply_prime_pow (i := 1) hp)

theorem B_prime (p : ℕ) (hp : p.Prime) : B p = p + 2 := by
  simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using B_pow p 1 hp

theorem sum_two (k : ℕ) : (∑ j ∈ Finset.range (k + 1), 2 ^ j) + 1 = 2 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ _ (k + 1), pow_succ (2 : ℕ) (k + 1)]
    omega

theorem double_sum_two (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (i + 1), 2 ^ j) + (k + 3) =
      2 ^ (k + 2) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ _ (k + 1)]
    have hs := sum_two (k + 1)
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ (2 : ℕ) (k + 2)]
    simp only [Nat.add_assoc, Nat.reduceAdd] at hs ⊢
    omega

theorem sigma_two14 : sigma 1 (2 ^ 14) = 32767 := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  have h := sum_two 14
  change (∑ j ∈ Finset.range (14 + 1), 2 ^ j) + 1 = 32768 at h
  omega

theorem B_two14 : B (2 ^ 14) = 65519 := by
  rw [B_pow 2 14 Nat.prime_two]
  have h := double_sum_two 14
  change (∑ i ∈ Finset.range (14 + 1), ∑ j ∈ Finset.range (i + 1), 2 ^ j) + 17 = 65536 at h
  omega

theorem prime_4409 : Nat.Prime 4409 := by norm_num

theorem prime_458009 : Nat.Prime 458009 := by norm_num

theorem coprime_one : Nat.Coprime (2 ^ 14) 4409 := by norm_num

theorem coprime_two : Nat.Coprime (2 ^ 14 * 4409) 458009 := by norm_num

-- Perform all divisor-sum rewrites with symbolic odd factors, so that
-- no reduction of the divisor set of the large witness is needed.
theorem formula (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hc1 : Nat.Coprime (2 ^ 14) p) (hc2 : Nat.Coprime (2 ^ 14 * p) q) :
    a (2 ^ 14 * p * q) =
      2 * (32767 * (p + 1) * (q + 1) : ℕ) - (65519 * (p + 2) * (q + 2) : ℕ) := by
  rw [a_eq, isMultiplicative_sigma.map_mul_of_coprime hc2,
    isMultiplicative_sigma.map_mul_of_coprime hc1,
    B_mult.map_mul_of_coprime hc2, B_mult.map_mul_of_coprime hc1,
    sigma_two14, B_two14, sigma_prime p hp, sigma_prime q hq,
    B_prime p hp, B_prime q hq]

-- 33085221781504 is a solution distinct from both 1 and 12.
theorem value : a (2 ^ 14 * 4409 * 458009) = 1 :=
  (formula 4409 458009 prime_4409 prime_458009 coprime_one coprime_two).trans (by norm_num)

end A296075Counterexample

theorem oeis_296075_conjecture_0.disproof : ¬ (type_of% @oeis_296075_conjecture_0) := by
  intro h
  have hfalse := (h (2 ^ 14 * 4409 * 458009)).mp A296075Counterexample.value
  norm_num at hfalse
