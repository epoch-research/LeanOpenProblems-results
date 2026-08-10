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

open ArithmeticFunction

/--
Disproof of the OEIS A296075 conjecture (by Robert Israel) that 1 and 12 are the
only solutions to `a(n) = 1`.

Counterexample: `N = 33085221781504 = 2^14 · 4409 · 458009` also satisfies `a(N) = 1`,
yet `N ∉ {1, 12}`.

Indeed `a(n) = 2·σ(n) - S(n)` where `S(n) = ∑_{d|n} σ(d)`, both `σ` and `S = ζ * σ`
are multiplicative, and for `N` we have `σ(N) = 32767·4410·458010 = 66183576284700`
and `S(N) = 65519·4411·458011 = 132367152569399`, giving `a(N) = 1`.
-/
-- All required numerical facts are verified in the kernel via `decide` / `norm_num`
-- using the prime-power factorisation of `N`, so no extra axioms are introduced.

private lemma aux_c1 : Nat.Coprime 16384 (4409 * 458009) := by decide
private lemma aux_c2 : Nat.Coprime 4409 458009 := by decide

/-- The divisor-sum of `σ` over a prime power, reduced to a small double sum. -/
private lemma S_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (∑ d ∈ (p ^ k).divisors, ArithmeticFunction.sigma 1 d)
      = ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (j + 1), p ^ i := by
  rw [sum_divisors_prime_pow hp]
  exact Finset.sum_congr rfl fun j _ => sigma_one_apply_prime_pow hp

-- `σ` of the prime-power factors of `N`.
private lemma aux_sig_16384 : ArithmeticFunction.sigma 1 16384 = 32767 := by
  rw [show (16384 : ℕ) = 2 ^ 14 by norm_num,
      sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]; decide
private lemma aux_sig_4409 : ArithmeticFunction.sigma 1 4409 = 4410 := by
  rw [show (4409 : ℕ) = 4409 ^ 1 by norm_num,
      sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4409)]; decide
private lemma aux_sig_458009 : ArithmeticFunction.sigma 1 458009 = 458010 := by
  rw [show (458009 : ℕ) = 458009 ^ 1 by norm_num,
      sigma_one_apply_prime_pow (by norm_num : Nat.Prime 458009)]; decide

-- `S = ∑_{d|·} σ(d)` of the prime-power factors of `N`.
private lemma aux_S_16384 :
    (∑ d ∈ Nat.divisors 16384, ArithmeticFunction.sigma 1 d) = 65519 := by
  rw [show (16384 : ℕ) = 2 ^ 14 by norm_num, S_prime_pow (by norm_num : Nat.Prime 2) 14]; decide
private lemma aux_S_4409 :
    (∑ d ∈ Nat.divisors 4409, ArithmeticFunction.sigma 1 d) = 4411 := by
  rw [show (4409 : ℕ) = 4409 ^ 1 by norm_num, S_prime_pow (by norm_num : Nat.Prime 4409) 1]; decide
private lemma aux_S_458009 :
    (∑ d ∈ Nat.divisors 458009, ArithmeticFunction.sigma 1 d) = 458011 := by
  rw [show (458009 : ℕ) = 458009 ^ 1 by norm_num,
      S_prime_pow (by norm_num : Nat.Prime 458009) 1]; decide

/-- Multiplicativity of the divisor-sum of `σ` (i.e. of `ζ * σ`), stated symbolically
so the Dirichlet convolution is never unfolded on concrete large numbers. -/
private lemma S_mul {m n : ℕ} (h : Nat.Coprime m n) :
    (∑ d ∈ (m * n).divisors, ArithmeticFunction.sigma 1 d)
      = (∑ d ∈ m.divisors, ArithmeticFunction.sigma 1 d)
        * (∑ d ∈ n.divisors, ArithmeticFunction.sigma 1 d) := by
  have hm := isMultiplicative_zeta.mul (isMultiplicative_sigma (k := 1))
  rw [← zeta_mul_apply, ← zeta_mul_apply, ← zeta_mul_apply, hm.map_mul_of_coprime h]

/-- For the counterexample `N = 2^14 · 4409 · 458009`, we have `a N = 1`. -/
private lemma aux_aN : a 33085221781504 = 1 := by
  -- Step 1: `a N = 2 * (∑_{d|N} d) - (∑_{d|N} σ(d))`.
  have key : a 33085221781504
      = 2 * ((∑ d ∈ Nat.divisors 33085221781504, d : ℕ) : ℤ)
        - ((∑ d ∈ Nat.divisors 33085221781504, ArithmeticFunction.sigma 1 d : ℕ) : ℤ) := by
    unfold a
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    push_cast; ring
  rw [key]
  have hN : (33085221781504 : ℕ) = 16384 * (4409 * 458009) := by norm_num
  -- Step 2: `σ(N) = ∑_{d|N} d = 66183576284700` via multiplicativity of `σ`.
  have hsig : (∑ d ∈ Nat.divisors 33085221781504, d) = 66183576284700 := by
    rw [← sigma_one_apply, hN, isMultiplicative_sigma.map_mul_of_coprime aux_c1,
        isMultiplicative_sigma.map_mul_of_coprime aux_c2,
        aux_sig_16384, aux_sig_4409, aux_sig_458009]
    norm_num
  -- Step 3: `S(N) = ∑_{d|N} σ(d) = 132367152569399` via multiplicativity of `ζ * σ`.
  have hS : (∑ d ∈ Nat.divisors 33085221781504, ArithmeticFunction.sigma 1 d)
      = 132367152569399 := by
    rw [hN, S_mul aux_c1, S_mul aux_c2, aux_S_16384, aux_S_4409, aux_S_458009]
  rw [hsig, hS]; norm_num

theorem oeis_296075_conjecture_0.disproof : ¬ ∀ n : ℕ,
    a n = 1 ↔ n = 1 ∨ n = 12 := by
  intro h
  -- `a N = 1` forces `N = 1 ∨ N = 12`, which is false.
  rcases (h 33085221781504).mp aux_aN with h1 | h2
  · norm_num at h1
  · norm_num at h2
