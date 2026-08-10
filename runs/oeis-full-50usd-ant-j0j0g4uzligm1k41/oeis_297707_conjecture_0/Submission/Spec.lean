import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/--
A297707: $a(n) = \prod_{k=1}^{n-1} n!k$, where $n!k$ is $k$-tuple factorial of $n$.
The $k$-tuple factorial of $n$ is defined as
$$n!_k = \prod_{j=0}^{\lfloor(n-1)/k\rfloor} (n - j k)$$
-/
def A297707 (n : ℕ) : ℕ :=
  let k_tuple_factorial (n k : ℕ) : ℕ :=
    if 0 < k then
      -- The number of terms is determined by the upper bound $\lfloor (n-1)/k \rfloor$.
      let max_j : ℕ := (n - 1) / k
      Finset.prod (range (max_j + 1)) fun j => n - j * k
    else
      1 -- Case k=0 is not used in the sequence, but we must be total.

  -- The overall sequence is $\prod_{k=1}^{n-1} n!_k$, given by Ico 1 n.
  Finset.prod (Ico 1 n) fun k => k_tuple_factorial n k

/-- A natural number greater than 1 that is not prime. -/
def IsComposite (n : ℕ) : Prop := 1 < n ∧ ¬ Nat.Prime n

/-- The largest prime number strictly less than `n`.
    Returns 0 if no such prime exists (i.e., n ≤ 2). -/
noncomputable def Nat.prevPrime (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range n)).max.getD 0

local notation "a" => A297707

/-!
### Structural analysis of the conjecture

The key structural fact is that `a n` is `n`-smooth (indeed `n ! ∣ a n`, coming
from the `k = 1` factor which is exactly `n !`).  Consequently the difference
`D = a n - prevPrime (a n)` is *coprime to every prime `≤ n`*, so a composite `D`
must be at least `(n+1)²`.  This reduces the conjecture to the prime-gap
statement: for every `n` with `3 ≤ n ≤ 250` there is a prime in the interval
`(a n - (n+1)², a n)`.
-/

/-- The `k = 1` factor of `A297707 n` is exactly `n !`. -/
theorem ktf_one (n : ℕ) (hn : 1 ≤ n) :
    (Finset.prod (range ((n - 1) / 1 + 1)) fun j => n - j * 1) = n ! := by
  simp only [Nat.div_one, mul_one]
  have : (n - 1) + 1 = n := by omega
  rw [this, ← Nat.descFactorial_eq_prod_range n n, Nat.descFactorial_self]

/-- `n ! ∣ a n` for `n ≥ 2`. -/
theorem factorial_dvd (n : ℕ) (hn : 2 ≤ n) : n ! ∣ a n := by
  have h1 : (1 : ℕ) ∈ Finset.Ico 1 n := by
    simp only [Finset.mem_Ico]; omega
  have := Finset.dvd_prod_of_mem
    (fun k => if 0 < k then Finset.prod (range ((n - 1) / k + 1)) fun j => n - j * k else 1) h1
  simp only [if_pos (by norm_num : (0 : ℕ) < 1)] at this
  rw [ktf_one n (by omega)] at this
  convert this using 2

/-- Every prime `≤ n` divides `a n`. -/
theorem prime_dvd_a {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime) (hpn : p ≤ n) : p ∣ a n :=
  (hp.dvd_factorial.mpr hpn).trans (factorial_dvd n hn)

theorem prevPrime_eq {N : ℕ}
    (hne : (Finset.filter Nat.Prime (Finset.range N)).Nonempty) :
    Nat.prevPrime N = (Finset.filter Nat.Prime (Finset.range N)).max' hne := by
  unfold Nat.prevPrime
  rw [← Finset.coe_max' hne]; rfl

/-- `prevPrime N` is prime, provided some prime lies below `N`. -/
theorem prevPrime_prime {N : ℕ} (h : ∃ p < N, p.Prime) : (Nat.prevPrime N).Prime := by
  obtain ⟨p, hpN, hp⟩ := h
  have hne : (Finset.filter Nat.Prime (Finset.range N)).Nonempty :=
    ⟨p, by simp [Finset.mem_filter, Finset.mem_range, hpN, hp]⟩
  rw [prevPrime_eq hne]
  exact (Finset.mem_filter.mp ((Finset.filter Nat.Prime (Finset.range N)).max'_mem hne)).2

/-- `prevPrime N` dominates every prime below `N`. -/
theorem le_prevPrime {N p : ℕ} (hp : p.Prime) (hpN : p < N) : p ≤ Nat.prevPrime N := by
  have hne : (Finset.filter Nat.Prime (Finset.range N)).Nonempty :=
    ⟨p, by simp [Finset.mem_filter, Finset.mem_range, hpN, hp]⟩
  rw [prevPrime_eq hne]
  exact Finset.le_max' _ p (by simp [Finset.mem_filter, Finset.mem_range, hpN, hp])

theorem prevPrime_lt {N : ℕ} (h : ∃ p < N, p.Prime) : Nat.prevPrime N < N := by
  obtain ⟨p, hpN, hp⟩ := h
  have hne : (Finset.filter Nat.Prime (Finset.range N)).Nonempty :=
    ⟨p, by simp [Finset.mem_filter, Finset.mem_range, hpN, hp]⟩
  rw [prevPrime_eq hne]
  exact Finset.mem_range.mp
    (Finset.mem_filter.mp ((Finset.filter Nat.Prime (Finset.range N)).max'_mem hne)).1

/-- `a n` is positive (all factors `n - j*k` are `≥ 1`). -/
theorem a_pos (n : ℕ) : 0 < a n := by
  apply Finset.prod_pos
  intro k hk
  rw [Finset.mem_Ico] at hk
  simp only [if_pos (show 0 < k by omega)]
  apply Finset.prod_pos
  intro j hj
  rw [Finset.mem_range] at hj
  have : j * k ≤ ((n - 1) / k) * k := Nat.mul_le_mul_right k (by omega)
  have h2 : ((n - 1) / k) * k ≤ n - 1 := Nat.div_mul_le_self _ _
  omega

/-- `n ! ≤ a n` for `n ≥ 2`. -/
theorem factorial_le_a (n : ℕ) (hn : 2 ≤ n) : n ! ≤ a n :=
  Nat.le_of_dvd (a_pos n) (factorial_dvd n hn)

theorem two_mul_lt_factorial (n : ℕ) (hn : 4 ≤ n) : 2 * n < n ! := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.factorial_succ]
  have h1 : m ≤ m ! := Nat.self_le_factorial m
  have h2 : 0 < m ! := Nat.factorial_pos m
  nlinarith [h1, h2]

/-- `2 n < a n` for `n ≥ 3`; hence Bertrand's prime `≤ 2n` lies strictly below `a n`. -/
theorem two_mul_lt_a (n : ℕ) (hn : 3 ≤ n) : 2 * n < a n := by
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · interval_cases n <;> decide
  · exact lt_of_lt_of_le (two_mul_lt_factorial n h4) (factorial_le_a n (by omega))

/-- `prevPrime (a n)` is prime, exceeds `n`, and is `< a n`, for `n ≥ 3`. -/
theorem prevPrime_props (n : ℕ) (hn : 3 ≤ n) :
    (Nat.prevPrime (a n)).Prime ∧ n < Nat.prevPrime (a n) ∧ Nat.prevPrime (a n) < a n := by
  obtain ⟨p, hp, hnp, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hpan : p < a n := lt_of_le_of_lt hp2n (two_mul_lt_a n hn)
  have hex : ∃ p < a n, p.Prime := ⟨p, hpan, hp⟩
  exact ⟨prevPrime_prime hex, lt_of_lt_of_le hnp (le_prevPrime hp hpan), prevPrime_lt hex⟩

/-- **Coprimality.**  No prime `≤ n` divides `D = a n - prevPrime (a n)`.
    (Because `p ∣ a n` while `p ∤ prevPrime (a n)`, the latter being a prime `> n`.) -/
theorem coprime_diff (n : ℕ) (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    ¬ p ∣ (a n - Nat.prevPrime (a n)) := by
  obtain ⟨hqp, hnq, hqa⟩ := prevPrime_props n hn
  intro hdvd
  have hpan : p ∣ a n := prime_dvd_a (by omega) hp hpn
  have hpq : p ∣ Nat.prevPrime (a n) := by
    have := Nat.dvd_sub hpan hdvd
    rwa [Nat.sub_sub_self (le_of_lt hqa)] at this
  have : p = Nat.prevPrime (a n) := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq
  omega

/-- oeis_297707_conjecture_0: What is the least n > 2 for which a(n) - prevprime(a(n)) is a composite number?
If such a number n exists, it is greater than 250. -/
theorem oeis_297707_conjecture_0 :
  ∀ n, 2 < n → IsComposite (a n - Nat.prevPrime (a n)) → 250 < n :=
by
  intro n hn hcomp
  by_contra hle
  push_neg at hle
  have hn3 : 3 ≤ n := by omega
  set D := a n - Nat.prevPrime (a n) with hDdef
  obtain ⟨hD1, hDnp⟩ := hcomp
  -- The least prime factor of `D` is prime and, by coprimality, exceeds `n`.
  have hmfp : (Nat.minFac D).Prime := Nat.minFac_prime (by omega)
  have hmf_gt : n < Nat.minFac D := by
    by_contra hc
    push_neg at hc
    exact coprime_diff n hn3 hmfp hc (Nat.minFac_dvd D)
  -- A composite number is at least the square of its least prime factor.
  have hsq : Nat.minFac D ^ 2 ≤ D := Nat.minFac_sq_le_self (by omega) hDnp
  have hDbig : (n + 1) ^ 2 ≤ D := le_trans (by nlinarith [hmf_gt]) hsq
  -- Remaining: for `3 ≤ n ≤ 250` the prime gap below `a n` is `< (n+1)²`
  -- (a prime lies in `(a n - (n+1)², a n)`), contradicting `hDbig`.
  sorry

