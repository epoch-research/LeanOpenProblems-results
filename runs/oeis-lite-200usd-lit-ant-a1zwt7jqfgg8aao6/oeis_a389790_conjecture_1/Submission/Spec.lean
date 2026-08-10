import FormalConjectures.Util.ProblemImports
open Classical
open Nat

/-- The smallest prime strictly greater than $r$. Defined non-computably using the set infimum. -/
noncomputable def next_prime (r : ℕ) : ℕ :=
  -- Nat.sInf finds the minimum element in a set of natural numbers.
  -- The set of primes greater than r is non-empty by Euclid's theorem.
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

/-- $r + r'$, where $r'$ is the next prime after $r$. -/
noncomputable def S_sum (r : ℕ) : ℕ := r + next_prime r

/--
A389790: Number of ways to write $2n$ as $p + p' + q + q'$, where $p$ and $q$ are primes with $p \le q$, and $r'$ is the first prime greater than $r$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let target := 2 * n
  -- The finset range is taken from the original user code.
  let R := Finset.range n

  Finset.card $ Finset.filter (fun ⟨p, q⟩ =>
    Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = target
  ) (R ×ˢ R)

/-! ###  Reducible structure (rigorously proven, unconditional)

We prove all of the reducible structure of the problem. In particular the
`Finset.range n` bound in the definition of `a` is *redundant*: any pair of
primes `p ≤ q` with `S_sum p + S_sum q = 2 * n` automatically has `p, q < n`.
Hence `0 < a n` is equivalent to the pure additive statement that `2 * n` is a
sum of two "consecutive–prime sums" `S_sum p + S_sum q`. -/

/-- `next_prime r` is prime and strictly greater than `r`. -/
theorem next_prime_spec (r : ℕ) : Nat.Prime (next_prime r) ∧ r < next_prime r := by
  have hne : {k : ℕ | Nat.Prime k ∧ r < k}.Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (r + 1)
    exact ⟨p, hp2, hp1⟩
  exact Nat.sInf_mem hne

theorem lt_next_prime (r : ℕ) : r < next_prime r := (next_prime_spec r).2
theorem prime_next_prime (r : ℕ) : Nat.Prime (next_prime r) := (next_prime_spec r).1

/-- For any prime `p` one has `5 ≤ S_sum p` (since `p ≥ 2` and `next_prime p ≥ 3`). -/
theorem S_sum_ge_five {p : ℕ} (hp : Nat.Prime p) : 5 ≤ S_sum p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hnp2 : 2 ≤ next_prime p := (prime_next_prime p).two_le
  have hgt : p < next_prime p := lt_next_prime p
  have hnp3 : 3 ≤ next_prime p := by omega
  unfold S_sum; omega

/-- `2 * q < S_sum q` for every `q`, because `next_prime q > q`. -/
theorem two_mul_lt_S_sum (q : ℕ) : 2 * q < S_sum q := by
  have := lt_next_prime q; unfold S_sum; omega

/-- **Reduction lemma.** `0 < a n` iff `2 * n` is a sum `S_sum p + S_sum q` with
`p ≤ q` primes. The `Finset.range n` bound is redundant. -/
theorem a_pos_iff (n : ℕ) :
    0 < a n ↔ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = 2 * n := by
  constructor
  · intro h
    unfold a at h
    rw [Finset.card_pos] at h
    obtain ⟨⟨p, q⟩, hmem⟩ := h
    rw [Finset.mem_filter] at hmem
    exact ⟨p, q, hmem.2.1, hmem.2.2.1, hmem.2.2.2.1, hmem.2.2.2.2⟩
  · rintro ⟨p, q, hp, hq, hpq, hsum⟩
    have hq2 : 2 * q < S_sum q := two_mul_lt_S_sum q
    have hp5 : 5 ≤ S_sum p := S_sum_ge_five hp
    have hqn : q < n := by omega
    have hpn : p < n := lt_of_le_of_lt hpq hqn
    unfold a
    rw [Finset.card_pos]
    exact ⟨⟨p, q⟩, by
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hpn, hqn⟩, hp, hq, hpq, hsum⟩⟩

/-- OEIS A389790 Conjecture: a(n) > 0 for all n >= 474.
This is an analog of Goldbach's conjecture. It has been verified for n <= 2*10^5. -/
theorem oeis_a389790_conjecture_1 : ∀ n : ℕ, 474 ≤ n → 0 < a n := by
  sorry
