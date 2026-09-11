import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/--
A340079: $a(n) = n / \gcd(n, 1+A018804(n))$, where $A018804(n) = \sum_{k=1..n} \gcd(k, n)$.
$$a(n) = \frac{n}{\gcd(n, 1+\sum_{k=1}^n \gcd(k, n))}$$
-/
def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

/--
It is conjectured that $a(n) = 1$ if and only if $n$ is 1 or a prime number.
A340079: It is conjectured that this is 1 iff n is 1 or a prime. See _Thomas Ordowski_'s Oct 22 2014 comment in A018804.
-/
theorem oeis_340079_conjecture_0 (n : ℕ) : a n = 1 ↔ (n = 1 ∨ Nat.Prime n) := by
  sorry

/-- The conjecture is false: `n = 3 · 37 · 43 · 42307 · 116341 = 23492890653051` is composite but
`n ∣ 1 + ∑_{k=1}^{n} gcd(k, n)`, since for squarefree `n` the sum equals `∏ (2p - 1)` and here
`1 + ∏ (2p - 1) = 26 · n`. -/
theorem oeis_340079_conjecture_0.disproof : ¬ (type_of% @oeis_340079_conjecture_0) := by
  intro h
  -- Pillai's arithmetical function `P n = ∑_{k=1}^{n} gcd(k, n)`, obtained as the Dirichlet
  -- convolution `id * φ`; it is multiplicative and `P p = 2p - 1` for primes `p`.
  obtain ⟨P, hmult, hprime, hsum⟩ : ∃ P : ArithmeticFunction ℕ, P.IsMultiplicative ∧
      (∀ p : ℕ, p.Prime → P p = 2 * p - 1) ∧
      (∀ n : ℕ, 0 < n → ∑ k ∈ Ico 1 (n + 1), Nat.gcd k n = P n) := by
    have happly : ∀ n : ℕ,
        (ArithmeticFunction.id * ⟨Nat.totient, Nat.totient_zero⟩ : ArithmeticFunction ℕ) n =
          ∑ d ∈ n.divisors, d * φ (n / d) := by
      intro n
      rw [ArithmeticFunction.mul_apply]
      exact Nat.sum_divisorsAntidiagonal (fun a b => a * φ b)
    refine ⟨ArithmeticFunction.id * ⟨Nat.totient, Nat.totient_zero⟩, ?_, ?_, ?_⟩
    · exact ArithmeticFunction.isMultiplicative_id.mul
        ⟨Nat.totient_one, fun h => Nat.totient_mul h⟩
    · intro p hp
      rw [happly, hp.divisors, Finset.sum_pair hp.ne_one.symm, Nat.div_one, Nat.div_self hp.pos,
        Nat.totient_prime hp, Nat.totient_one, one_mul, mul_one, two_mul,
        ← Nat.sub_add_comm hp.one_le]
    · intro n hn
      have key : ∑ k ∈ range n, Nat.gcd n k = ∑ d ∈ n.divisors, d * φ (n / d) := by
        rw [← Finset.sum_fiberwise_of_maps_to (s := range n) (t := n.divisors)
          (g := fun k => Nat.gcd n k)
          (fun x _ => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left _ _, hn.ne'⟩)]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]
        rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.1 hx).2), Finset.sum_const,
          smul_eq_mul, mul_comm]
      rw [happly, ← key, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn,
        Finset.sum_Ico_succ_top hn, Nat.gcd_zero_right, Nat.gcd_self, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun k _ => Nat.gcd_comm _ _
  -- If `n ∣ 1 + P n` then `a n = 1`.
  have ha : ∀ n : ℕ, 0 < n → n ∣ 1 + P n → a n = 1 := by
    intro n hn hd
    show n / Nat.gcd n (1 + ∑ k ∈ Ico 1 (n + 1), Nat.gcd k n) = 1
    rw [hsum n hn, Nat.gcd_eq_left hd, Nat.div_self hn]
  -- Evaluate `P` at the counterexample using multiplicativity.
  have hP : P 23492890653051 = 610815156979325 := by
    have e : (23492890653051 : ℕ) = ((((3 * 37) * 43) * 42307) * 116341) := by norm_num
    rw [e, hmult.map_mul_of_coprime (by norm_num), hmult.map_mul_of_coprime (by norm_num),
      hmult.map_mul_of_coprime (by norm_num), hmult.map_mul_of_coprime (by norm_num),
      hprime _ (by norm_num), hprime _ (by norm_num), hprime _ (by norm_num),
      hprime _ (by norm_num), hprime _ (by norm_num)]
    norm_num
  have hval : a 23492890653051 = 1 :=
    ha _ (Nat.succ_pos _) (hP ▸ Dvd.intro 26 (by norm_num))
  have hnp : ¬ Nat.Prime 23492890653051 :=
    (by norm_num : (23492890653051 : ℕ) = 3 * 7830963551017) ▸
      Nat.not_prime_mul (by norm_num) (by norm_num)
  rcases (h 23492890653051).1 hval with h1 | h1
  · exact absurd h1 (by norm_num)
  · exact hnp h1

