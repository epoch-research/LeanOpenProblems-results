import FormalConjectures.Util.ProblemImports

open Nat
open ArithmeticFunction
open scoped ArithmeticFunction.zeta

/--
A296075: Sum of deficiencies of divisors of $n$.
The deficiency of a number $d$ is $2d - \sigma_1(d)$, where $\sigma_1(d)$ is the sum of the divisors of $d$.
$$a(n) = \sum_{d|n} (2d - \sigma_1(d))$$
-/
def a (n : ℕ) : ℤ :=
  (divisors n).sum fun d =>
    -- Deficiency of d: 2*d - sigma_1(d)
    (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)

/-!
The OEIS A296075 conjecture by Robert Israel asks whether `1` and `12` are the only
solutions to `a(n) = 1`.  This is **false**:
`n = 33085221781504 = 2^14 * 4409 * 458009` also satisfies `a(n) = 1`.

We verify this counterexample below (working with the multiplicative structure of the
relevant divisor sums) and deduce that the conjectured equivalence fails.
-/

/-- The function `n ↦ ∑_{d ∣ n} σ₁(d)` is multiplicative: it splits over coprime factors. -/
private lemma sumdiv_mul {m n : ℕ} (h : Nat.Coprime m n) :
    ∑ d ∈ (m * n).divisors, ArithmeticFunction.sigma 1 d
    = (∑ d ∈ m.divisors, ArithmeticFunction.sigma 1 d) *
      (∑ d ∈ n.divisors, ArithmeticFunction.sigma 1 d) := by
  have key := (isMultiplicative_zeta.mul (isMultiplicative_sigma (k := 1))).map_mul_of_coprime h
  rw [zeta_mul_apply, zeta_mul_apply, zeta_mul_apply] at key
  exact key

private lemma Fp14 : ∑ d ∈ (2 ^ 14).divisors, ArithmeticFunction.sigma 1 d = 65519 := by
  rw [sum_divisors_prime_pow Nat.prime_two,
    Finset.sum_congr rfl (fun x _ => sigma_one_apply_prime_pow Nat.prime_two (p := 2) (i := x))]
  simp [Finset.sum_range_succ]

private lemma F4409 : ∑ d ∈ (4409 : ℕ).divisors, ArithmeticFunction.sigma 1 d = 4411 := by
  rw [(by norm_num : Nat.Prime 4409).divisors, Finset.sum_pair (by norm_num), sigma_one]
  rw [sigma_one_apply, (by norm_num : Nat.Prime 4409).divisors, Finset.sum_pair (by norm_num)]
  norm_num

private lemma F458009 : ∑ d ∈ (458009 : ℕ).divisors, ArithmeticFunction.sigma 1 d = 458011 := by
  rw [(by norm_num : Nat.Prime 458009).divisors, Finset.sum_pair (by norm_num), sigma_one]
  rw [sigma_one_apply, (by norm_num : Nat.Prime 458009).divisors, Finset.sum_pair (by norm_num)]
  norm_num

/-- `∑_{d ∣ 33085221781504} σ₁(d) = 132367152569399`. -/
private lemma Fn : ∑ d ∈ (33085221781504 : ℕ).divisors, ArithmeticFunction.sigma 1 d
    = 132367152569399 := by
  rw [(by norm_num : (33085221781504 : ℕ) = 2 ^ 14 * (4409 * 458009)),
    sumdiv_mul (by norm_num : Nat.Coprime (2 ^ 14) (4409 * 458009)),
    sumdiv_mul (by norm_num : Nat.Coprime 4409 458009), Fp14, F4409, F458009]

private lemma Sp14 : ∑ d ∈ (2 ^ 14).divisors, d = 32767 := by
  rw [sum_divisors_prime_pow Nat.prime_two]; simp [Finset.sum_range_succ]

private lemma S4409 : ∑ d ∈ (4409 : ℕ).divisors, d = 4410 := by
  rw [(by norm_num : Nat.Prime 4409).divisors, Finset.sum_pair (by norm_num)]

private lemma S458009 : ∑ d ∈ (458009 : ℕ).divisors, d = 458010 := by
  rw [(by norm_num : Nat.Prime 458009).divisors, Finset.sum_pair (by norm_num)]

/-- `σ₁(33085221781504) = ∑_{d ∣ 33085221781504} d = 66183576284700`. -/
private lemma Sn : ∑ d ∈ (33085221781504 : ℕ).divisors, d = 66183576284700 := by
  rw [(by norm_num : (33085221781504 : ℕ) = 2 ^ 14 * (4409 * 458009)),
    Nat.Coprime.sum_divisors_mul (by norm_num : Nat.Coprime (2 ^ 14) (4409 * 458009)),
    Nat.Coprime.sum_divisors_mul (by norm_num : Nat.Coprime 4409 458009), Sp14, S4409, S458009]

/-- The counterexample: `a(2^14 * 4409 * 458009) = 1`. -/
private lemma a_counter : a 33085221781504 = 1 := by
  unfold a
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Nat.cast_sum, ← Nat.cast_sum, Sn, Fn]
  norm_num

/--
Disproof of the OEIS A296075 conjecture: `1` and `12` are **not** the only solutions of
`a(n) = 1`, since `a(33085221781504) = 1` while `33085221781504 ∉ {1, 12}`.
-/
theorem oeis_296075_conjecture_0.disproof : ¬ ∀ n : ℕ,
    a n = 1 ↔ n = 1 ∨ n = 12 := by
  intro h
  rcases (h 33085221781504).mp a_counter with h3 | h3 <;> norm_num at h3
