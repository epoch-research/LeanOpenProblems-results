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

/-
Disproof of the conjecture from OEIS A296075 (by Robert Israel):
"Are 1 and 12 the only solutions to a(n)=1?"

The answer is NO: the number
  n₀ = 33085221781504 = 2^14 * 4409 * 458009
also satisfies a(n₀) = 1 (and n₀ ≠ 1, n₀ ≠ 12).

Indeed, writing b(n) = ∑_{d ∣ n} σ₁(d) (which is the Dirichlet convolution σ₁ * ζ,
hence multiplicative), we have a(n) = 2σ₁(n) - b(n), and
  σ₁(2^14) = 32767,   b(2^14) = 65519,
  σ₁(4409) = 4410,    b(4409) = 4411      (4409 is prime),
  σ₁(458009) = 458010, b(458009) = 458011 (458009 is prime),
so that
  a(n₀) = 2 * 32767 * 4410 * 458010 - 65519 * 4411 * 458011 = 1.
-/

namespace Disproof296075

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.zeta

/-- `bfun n = ∑_{d ∣ n} σ₁(d)`. -/
def bfun (n : ℕ) : ℕ := ∑ d ∈ n.divisors, σ 1 d

lemma bfun_eq (n : ℕ) : bfun n = (σ 1 * ζ) n := by
  rw [bfun, mul_zeta_apply]

lemma isMultiplicative_bfun : IsMultiplicative (σ 1 * ζ) :=
  isMultiplicative_sigma.mul isMultiplicative_zeta

lemma bfun_mul {m n : ℕ} (h : m.Coprime n) : bfun (m * n) = bfun m * bfun n := by
  rw [bfun_eq, bfun_eq, bfun_eq, isMultiplicative_bfun.map_mul_of_coprime h]

lemma sigma_mul {m n : ℕ} (h : m.Coprime n) : σ 1 (m * n) = σ 1 m * σ 1 n :=
  isMultiplicative_sigma.map_mul_of_coprime h

lemma a_eq (n : ℕ) : a n = 2 * (σ 1 n : ℤ) - (bfun n : ℤ) := by
  rw [a, bfun, sigma_one_apply]
  push_cast
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  rw [sigma_one_apply, hp.divisors, Finset.sum_insert (by simp [hp.one_lt.ne]),
    Finset.sum_singleton]
  omega

lemma bfun_prime {p : ℕ} (hp : p.Prime) : bfun p = p + 2 := by
  rw [bfun, hp.divisors, Finset.sum_insert (by simp [hp.one_lt.ne]), Finset.sum_singleton,
    sigma_one_prime hp, sigma_one_apply, Nat.divisors_one]
  simp
  omega

lemma sigma_pow2_14 : σ 1 16384 = 32767 := by
  have : (16384 : ℕ) = 2 ^ 14 := by norm_num
  rw [this, sigma_one_apply_prime_pow Nat.prime_two]
  decide

lemma bfun_pow2_14 : bfun 16384 = 65519 := by
  have h : (16384 : ℕ) = 2 ^ 14 := by norm_num
  rw [bfun, h, Nat.sum_divisors_prime_pow Nat.prime_two]
  have : ∀ i, σ 1 (2 ^ i) = 2 ^ (i + 1) - 1 := by
    intro i
    rw [sigma_one_apply_prime_pow Nat.prime_two, Nat.geomSum_eq (le_refl 2)]
    simp
  simp only [this]
  decide

lemma h4409 : Nat.Prime 4409 := by norm_num
lemma h458009 : Nat.Prime 458009 := by norm_num

/-- The counterexample: `a (2^14 * 4409 * 458009) = 1`. -/
lemma key : a 33085221781504 = 1 := by
  have h1 : (33085221781504 : ℕ) = 16384 * 4409 * 458009 := by norm_num
  have hc1 : Nat.Coprime (16384 * 4409) 458009 := by norm_num
  have hc2 : Nat.Coprime 16384 4409 := by norm_num
  rw [h1, a_eq, sigma_mul hc1, sigma_mul hc2, bfun_mul hc1, bfun_mul hc2,
    sigma_one_prime h4409, sigma_one_prime h458009, bfun_prime h4409, bfun_prime h458009,
    sigma_pow2_14, bfun_pow2_14]
  norm_num

end Disproof296075

/--
Conjecture from OEIS A296075, by Robert Israel:
Are 1 and 12 the only solutions to a(n)=1?

This is FALSE: `n = 33085221781504 = 2^14 * 4409 * 458009` is a further solution.
-/
theorem oeis_296075_conjecture_0.disproof : ¬ (∀ n : ℕ,
    a n = 1 ↔ n = 1 ∨ n = 12) := by
  intro h
  have := (h 33085221781504).mp Disproof296075.key
  norm_num at this
