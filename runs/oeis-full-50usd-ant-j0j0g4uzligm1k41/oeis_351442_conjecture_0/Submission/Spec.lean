import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A003958 is a multiplicative function defined by $A003958(p^e) = (p-1)^e$ for a prime power $p^e$.
For $n = \prod p_i^{e_i}$, $A003958(n) = \prod (p_i - 1)^{e_i}$.
-/
def A003958 (n : ℕ) : ℕ :=
  n.factorization.prod fun p e => (p - 1) ^ e

/--
A351442: $a(n) = A003958(\sigma(n))$, where $A003958$ is multiplicative with $a(p^e) = (p-1)^e$
and $\sigma$ is the sum of divisors function.
-/
def a (n : ℕ) : ℕ :=
  A003958 (ArithmeticFunction.sigma 1 n)

/-!
`oeis_351442_conjecture_0` conjectured that the positive fixed points of `a` are
*exactly* `{1, 2, 8, 128, 288, 720, 32768, 29719872, 2147483648}`.

This is **false**: there is a further fixed point
`N = 28996592704045424640 = 2^13 · 3^6 · 5 · 7^6 · 13^4 · 17^2`.
Indeed
`σ(N) = 140078688585537333726 = 2 · 3^2 · 29 · 43 · 127 · 307 · 1093 · 4733 · 30941`,
and `A003958(σ(N)) = 1^1 · 2^2 · 28 · 42 · 126 · 306 · 1092 · 4732 · 30940 = N`,
so `a N = N` while `N` is not in the list.

Below we prove the negation of the conjecture.
-/

/-- `A003958` of a prime power: `A003958 (p ^ e) = (p - 1) ^ e`. -/
theorem A003958_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    A003958 (p ^ e) = (p - 1) ^ e := by
  unfold A003958
  rw [hp.factorization_pow, Finsupp.prod_single_index]
  simp

/-- `A003958` is (completely) multiplicative on nonzero arguments, since the prime
factorization of a product is the sum of the factorizations. -/
theorem A003958_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    A003958 (m * n) = A003958 m * A003958 n := by
  unfold A003958
  rw [Nat.factorization_mul hm hn, Finsupp.prod_add_index']
  · intro a; simp
  · intro a b1 b2; rw [pow_add]

/-- `A003958` of a prime: `A003958 p = p - 1`. -/
theorem A003958_prime {p : ℕ} (hp : p.Prime) : A003958 p = p - 1 := by
  have h : A003958 p = A003958 (p ^ 1) := by rw [pow_one]
  rw [h, A003958_prime_pow hp, pow_one]

/-- The number `N = 2^13 · 3^6 · 5 · 7^6 · 13^4 · 17^2` is a fixed point of `a`. -/
theorem a_counterexample : a 28996592704045424640 = 28996592704045424640 := by
  unfold a
  have hs : ArithmeticFunction.sigma 1 28996592704045424640 = 140078688585537333726 := by
    have h : (28996592704045424640 : ℕ)
        = 2 ^ 13 * (3 ^ 6 * (5 ^ 1 * (7 ^ 6 * (13 ^ 4 * 17 ^ 2)))) := by norm_num
    rw [h, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    decide
  rw [hs]
  have h : (140078688585537333726 : ℕ)
      = 2 ^ 1 * (3 ^ 2 * (29 * (43 * (127 * (307 * (1093 * (4733 * 30941))))))) := by norm_num
  rw [h, A003958_mul (by norm_num) (by norm_num),
    A003958_mul (by norm_num) (by norm_num),
    A003958_mul (by norm_num) (by norm_num),
    A003958_mul (by norm_num) (by norm_num),
    A003958_mul (by norm_num) (by norm_num),
    A003958_mul (by norm_num) (by norm_num),
    A003958_mul (by norm_num) (by norm_num),
    A003958_mul (by norm_num) (by norm_num),
    A003958_prime_pow (by norm_num : Nat.Prime 2),
    A003958_prime_pow (by norm_num : Nat.Prime 3),
    A003958_prime (by norm_num : Nat.Prime 29),
    A003958_prime (by norm_num : Nat.Prime 43),
    A003958_prime (by norm_num : Nat.Prime 127),
    A003958_prime (by norm_num : Nat.Prime 307),
    A003958_prime (by norm_num : Nat.Prime 1093),
    A003958_prime (by norm_num : Nat.Prime 4733),
    A003958_prime (by norm_num : Nat.Prime 30941)]
  norm_num

/--
The conjecture `oeis_351442_conjecture_0` is false: `28996592704045424640` is a
positive fixed point of `a` that does not belong to the proposed list.
-/
theorem oeis_351442_conjecture_0.disproof :
    ¬ (∀ n : ℕ, n > 0 → (a n = n ↔
      n ∈ ({1, 2, 8, 128, 288, 720, 32768, 29719872, 2147483648} : Finset ℕ))) := by
  intro h
  have hmem := (h 28996592704045424640 (by norm_num)).mp a_counterexample
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega
