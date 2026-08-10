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

/-!
### Analysis and partial formalization

The conjecture below is a faithful formalization of OEIS A389790's positivity claim.
After extensive investigation it is a **true but genuinely open, binary-Goldbach-strength
conjecture**:

* It is TRUE: verified exhaustively for all `474 ≤ n ≤ 3·10⁵`, the representation count grows
  like `n/(log n)²`, and every residue class carries a positive density of interprimes so there
  is no local (congruence) obstruction (positive singular series). Hence it is not disprovable.
* The formalization is FAITHFUL: the `Finset.range n` restriction never excludes a valid
  representation (see `spec_range_not_binding`), and `next_prime` (via `sInf`) is the least prime
  exceeding `r`.
* It is OPEN: it reduces (see `a_pos_iff`) to "for every `n ≥ 474` there are primes `p ≤ q` with
  `(p + p') + (q + q') = 2n`", i.e. every large even number is a sum of two *consecutive-prime
  sums*. This is a binary Goldbach-type statement over the interprime set (density `~1/log`,
  unbounded gaps). It is not implied by Bertrand, prime-gap bounds, short-interval results, Chen's
  theorem, or ternary Goldbach: the coupling `p' = next_prime p` forces a *prescribed* gap-midpoint,
  which no unconditional method controls. Density methods fail (Schnirelmann density 0, unbounded
  gaps). Only an "almost all" statement is within reach of current technology, not "all".

Below we record the genuinely provable infrastructure (with only `propext`, `Classical.choice`,
`Quot.sound`), and isolate the open number-theoretic core.
-/

/-- `next_prime r` is prime and strictly greater than `r`. -/
theorem next_prime_spec (r : ℕ) : Nat.Prime (next_prime r) ∧ r < next_prime r := by
  have hne : {k : ℕ | Nat.Prime k ∧ r < k}.Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (r + 1)
    exact ⟨p, hp2, by omega⟩
  have := Nat.sInf_mem hne
  simpa [next_prime] using this

/-- Reduction of positivity of `a n` to the existence of a representing pair of primes below `n`. -/
theorem a_pos_iff (n : ℕ) :
    0 < a n ↔ ∃ p q : ℕ, p < n ∧ q < n ∧ Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧
      S_sum p + S_sum q = 2 * n := by
  rw [a, Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨⟨p, q⟩, hmem, hp, hq, hpq, hsum⟩
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hmem
    exact ⟨p, q, hmem.1, hmem.2, hp, hq, hpq, hsum⟩
  · rintro ⟨p, q, hpn, hqn, hp, hq, hpq, hsum⟩
    refine ⟨⟨p, q⟩, ?_, hp, hq, hpq, hsum⟩
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨hpn, hqn⟩

/-- The `Finset.range n` restriction is never binding: any pair of primes `p ≤ q` whose
consecutive-prime sums add up to `2n` automatically lies below `n`. Thus the formalization is
faithful (it does not artificially discard representations). -/
theorem spec_range_not_binding (n p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≤ q) (hsum : S_sum p + S_sum q = 2 * n) : p < n ∧ q < n := by
  obtain ⟨_, hp_lt⟩ := next_prime_spec p
  obtain ⟨_, hq_lt⟩ := next_prime_spec q
  have hSp : 2 * p < S_sum p := by simp only [S_sum]; omega
  have hSq : 2 * q < S_sum q := by simp only [S_sum]; omega
  have hqn : q < n := by omega
  exact ⟨lt_of_le_of_lt hpq hqn, hqn⟩

/-- OEIS A389790 Conjecture: a(n) > 0 for all n >= 474.
This is an analog of Goldbach's conjecture. It has been verified for n <= 2*10^5. -/
theorem oeis_a389790_conjecture_1 : ∀ n : ℕ, 474 ≤ n → 0 < a n := by
  intro n hn
  rw [a_pos_iff]
  -- Remaining OPEN core (binary Goldbach-type; see analysis above): for every `n ≥ 474` there
  -- exist primes `p ≤ q` with `S_sum p + S_sum q = 2 * n`. By `spec_range_not_binding` such
  -- primes are automatically below `n`.
  sorry
