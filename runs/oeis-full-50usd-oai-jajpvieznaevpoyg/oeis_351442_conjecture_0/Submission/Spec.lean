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


lemma A003958_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    A003958 (m * n) = A003958 m * A003958 n := by
  unfold A003958
  rw [Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index' (by simp) (by simp [pow_add])

lemma A003958_prime_pow {p e : ℕ} (hp : Nat.Prime p) :
    A003958 (p ^ e) = (p - 1) ^ e := by
  unfold A003958
  rw [Nat.factorization_pow, hp.factorization]
  simp

/--
oeis_351442_conjecture_0: Question: Are there more fixed points than 1, 2, 8, 128, 288, 720, 32768, 29719872, ..., 2147483648 ?
This theorem conjectures that these numbers are exactly the positive fixed points of the sequence $a(n)$.
The list of fixed points is taken verbatim from the OEIS entry.
-/
theorem oeis_351442_conjecture_0.disproof :
  ¬ (∀ n : ℕ, n > 0 → (a n = n ↔ n ∈ ({1, 2, 8, 128, 288, 720, 32768, 29719872, 2147483648} : Finset ℕ))) := by
  intro h
  let N : ℕ := 28996592704045424640
  let S : ℕ := 140078688585537333726
  have hσ : ArithmeticFunction.sigma 1 N = S := by
    change ArithmeticFunction.sigma 1 (2^13 * 3^6 * 5^1 * 7^6 * 13^4 * 17^2) =
      140078688585537333726
    repeat rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_sigma (by norm_num)]
    repeat rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num)]
    norm_num
  have hA : A003958 S = N := by
    change A003958 (2^1 * 3^2 * 29^1 * 43^1 * 127^1 * 307^1 * 1093^1 * 4733^1 * 30941^1) =
      28996592704045424640
    repeat rw [A003958_mul (by norm_num) (by norm_num)]
    repeat rw [A003958_prime_pow (by norm_num)]
    norm_num
  have hfix : a N = N := by
    dsimp [a]
    rw [hσ]
    exact hA
  have hnot : ¬ N ∈ ({1, 2, 8, 128, 288, 720, 32768, 29719872, 2147483648} : Finset ℕ) := by
    norm_num [N]
  exact hnot ((h N (by norm_num [N])).mp hfix)
