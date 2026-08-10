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
Conjecture from OEIS A296075, by Robert Israel:
Are 1 and 12 the only solutions to a(n)=1?

This conjecture is FALSE.  A counterexample is
`n = 33085221781504 = 2^14 * 4409 * 458009`
(with `4409` and `458009` prime), for which `a(n) = 1` even though `n ∉ {1, 12}`.
Below we prove the negation of the conjecture.
-/

open scoped ArithmeticFunction.sigma
open scoped ArithmeticFunction
open ArithmeticFunction

namespace A296075Disproof

/-- `Sf = ζ * σ₁`, i.e. `Sf n = ∑_{d ∣ n} σ₁ d`.  It is multiplicative. -/
noncomputable def Sf : ArithmeticFunction ℕ :=
  ArithmeticFunction.zeta * ArithmeticFunction.sigma 1

theorem Sf_apply (n : ℕ) : Sf n = ∑ d ∈ divisors n, ArithmeticFunction.sigma 1 d := by
  rw [Sf, zeta_mul_apply]

theorem Sf_mult : Sf.IsMultiplicative := by
  rw [Sf]; exact isMultiplicative_zeta.mul isMultiplicative_sigma

/-- The key identity: `a n = 2 σ₁(n) - (∑_{d ∣ n} σ₁ d)`. -/
theorem a_eq (n : ℕ) : a n = 2 * (ArithmeticFunction.sigma 1 n : ℤ) - (Sf n : ℤ) := by
  rw [a, Sf_apply]
  rw [Finset.sum_sub_distrib]
  push_cast
  rw [← Finset.mul_sum]
  congr 1
  · rw [sigma_one_apply]
    push_cast
    ring

theorem sig_prime {p : ℕ} (hp : p.Prime) : ArithmeticFunction.sigma 1 p = p + 1 := by
  rw [sigma_one_apply, hp.divisors, Finset.sum_pair (by have := hp.two_le; omega)]
  omega

theorem Sf_prime {p : ℕ} (hp : p.Prime) : Sf p = p + 2 := by
  rw [Sf_apply, hp.divisors, Finset.sum_pair (by have := hp.two_le; omega)]
  rw [sig_prime hp, ArithmeticFunction.sigma_one 1]
  omega

theorem sig_two_pow : ArithmeticFunction.sigma 1 (2 ^ 14) = 32767 := by
  rw [sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
  decide

theorem Sf_two_pow : Sf (2 ^ 14) = 65519 := by
  rw [Sf_apply, Nat.sum_divisors_prime_pow (by norm_num : Nat.Prime 2)]
  simp only [sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
  decide

theorem sig_n0 : ArithmeticFunction.sigma 1 33085221781504 = 66183576284700 := by
  have e : (33085221781504 : ℕ) = 2 ^ 14 * 4409 * 458009 := by norm_num
  rw [e]
  rw [isMultiplicative_sigma.map_mul_of_coprime
      (show Nat.gcd (2 ^ 14 * 4409) 458009 = 1 by decide)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (show Nat.gcd (2 ^ 14) 4409 = 1 by decide)]
  rw [sig_two_pow, sig_prime (by norm_num), sig_prime (by norm_num)]
  norm_num

theorem Sf_n0 : Sf 33085221781504 = 132367152569399 := by
  have e : (33085221781504 : ℕ) = 2 ^ 14 * 4409 * 458009 := by norm_num
  rw [e]
  rw [Sf_mult.map_mul_of_coprime (show Nat.gcd (2 ^ 14 * 4409) 458009 = 1 by decide)]
  rw [Sf_mult.map_mul_of_coprime (show Nat.gcd (2 ^ 14) 4409 = 1 by decide)]
  rw [Sf_two_pow, Sf_prime (by norm_num), Sf_prime (by norm_num)]
  norm_num

/-- The counterexample: `a (2^14 * 4409 * 458009) = 1`. -/
theorem a_n0 : a 33085221781504 = 1 := by
  rw [a_eq, sig_n0, Sf_n0]
  norm_num

end A296075Disproof

/--
Disproof of the OEIS A296075 conjecture:
it is **not** the case that `a n = 1 ↔ n = 1 ∨ n = 12` for all `n`,
because `n = 33085221781504 = 2^14 * 4409 * 458009` satisfies `a n = 1` but is neither `1` nor `12`.
-/
theorem oeis_296075_conjecture_0.disproof : ¬ ∀ n : ℕ,
    a n = 1 ↔ n = 1 ∨ n = 12 := by
  intro h
  have := (h 33085221781504).mp A296075Disproof.a_n0
  rcases this with h1 | h12
  · norm_num at h1
  · norm_num at h12
