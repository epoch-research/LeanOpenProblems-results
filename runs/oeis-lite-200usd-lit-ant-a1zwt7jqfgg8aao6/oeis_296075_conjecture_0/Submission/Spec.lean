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

open ArithmeticFunction Finset

/-- The divisor sum of `σ₁`, i.e. `T n = ∑_{d ∣ n} σ₁(d)`, realised as the
Dirichlet convolution `ζ * σ₁`.  We give it a name so that the elaborator keeps
it atomic (and does not try to unfold the convolution at huge arguments). -/
def T : ArithmeticFunction ℕ := ArithmeticFunction.zeta * ArithmeticFunction.sigma 1

/-- `T` is multiplicative, being a product of multiplicative functions. -/
lemma T_isMultiplicative : T.IsMultiplicative :=
  isMultiplicative_zeta.mul isMultiplicative_sigma

/-- Evaluation of `T`: `T n = ∑_{d ∣ n} σ₁(d)`. -/
lemma T_apply (n : ℕ) : T n = ∑ d ∈ n.divisors, ArithmeticFunction.sigma 1 d :=
  ArithmeticFunction.zeta_mul_apply

/-- General reduction: `a n = 2·σ₁(n) - T(n)`. -/
lemma a_eq (n : ℕ) :
    a n = 2 * ((ArithmeticFunction.sigma 1 n : ℤ)) - (T n : ℤ) := by
  unfold a
  rw [Finset.sum_sub_distrib, T_apply, ArithmeticFunction.sigma_one_apply]
  push_cast
  rw [Finset.mul_sum]

set_option maxRecDepth 10000

/--
The conjecture from OEIS A296075 (by Robert Israel) asks whether `1` and `12`
are the only solutions to `a(n) = 1`.  This is **false**: the number
`33085221781504 = 2^14 · 4409 · 458009` is a further solution.  Indeed, by
multiplicativity of `σ₁` and of `T = ζ * σ₁`,
`σ₁(n₀) = 32767 · 4410 · 458010` and `T(n₀) = 65519 · 4411 · 458011`, so
`a(n₀) = 2·σ₁(n₀) - T(n₀) = 1`, while `n₀ ∉ {1, 12}`. -/
theorem oeis_296075_conjecture_0.disproof :
    ¬ (∀ n : ℕ, a n = 1 ↔ n = 1 ∨ n = 12) := by
  intro h
  have hp1 : Nat.Prime 4409 := by norm_num
  have hp2 : Nat.Prime 458009 := by norm_num
  have key : a 33085221781504 = 1 := by
    have hn : (33085221781504 : ℕ) = 2 ^ 14 * 4409 * 458009 := by norm_num
    -- σ₁ on each prime-power factor
    have s2 : ArithmeticFunction.sigma 1 (2 ^ 14) = 32767 := by
      rw [sigma_one_apply_prime_pow Nat.prime_two]; decide
    have s4 : ArithmeticFunction.sigma 1 4409 = 4410 := by
      have h : (4409 : ℕ) = 4409 ^ 1 := by norm_num
      rw [h, sigma_one_apply_prime_pow hp1]; decide
    have s5 : ArithmeticFunction.sigma 1 458009 = 458010 := by
      have h : (458009 : ℕ) = 458009 ^ 1 := by norm_num
      rw [h, sigma_one_apply_prime_pow hp2]; norm_num [Finset.sum_range_succ]
    -- T on each prime-power factor
    have t2 : T (2 ^ 14) = 65519 := by
      rw [T_apply, sum_divisors_prime_pow Nat.prime_two]
      simp only [sigma_one_apply_prime_pow Nat.prime_two]; decide
    have t4 : T 4409 = 4411 := by
      have h : (4409 : ℕ) = 4409 ^ 1 := by norm_num
      rw [h, T_apply, sum_divisors_prime_pow hp1]
      simp only [sigma_one_apply_prime_pow hp1]; norm_num [Finset.sum_range_succ]
    have t5 : T 458009 = 458011 := by
      have h : (458009 : ℕ) = 458009 ^ 1 := by norm_num
      rw [h, T_apply, sum_divisors_prime_pow hp2]
      simp only [sigma_one_apply_prime_pow hp2]; norm_num [Finset.sum_range_succ]
    -- coprimality facts
    have c1 : Nat.Coprime (2 ^ 14 * 4409) 458009 := by
      rw [Nat.coprime_comm, hp2.coprime_iff_not_dvd]; decide
    have c2 : Nat.Coprime (2 ^ 14) 4409 := by decide
    -- σ₁(n₀) and T(n₀) by multiplicativity
    have hsig : ArithmeticFunction.sigma 1 33085221781504 = 66183576284700 := by
      rw [hn, isMultiplicative_sigma.map_mul_of_coprime c1,
          isMultiplicative_sigma.map_mul_of_coprime c2, s2, s4, s5]
      norm_num
    have hT : T 33085221781504 = 132367152569399 := by
      rw [hn, T_isMultiplicative.map_mul_of_coprime c1,
          T_isMultiplicative.map_mul_of_coprime c2, t2, t4, t5]
      norm_num
    rw [a_eq, hsig, hT]; norm_num
  -- `33085221781504` is neither `1` nor `12`, contradicting the conjecture.
  have hmem := (h 33085221781504).mp key
  rcases hmem with h1 | h1 <;> norm_num at h1
