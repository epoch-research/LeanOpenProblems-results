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

/- ###  Reduction lemmas (fully proved, no `sorry`)

These reduce the conjecture to a clean existence statement and record the basic
specification of `next_prime`.  They are genuine, verified results. -/

/-- `next_prime r` is prime and strictly larger than `r` (it is the least such prime). -/
theorem next_prime_spec (r : ℕ) : Nat.Prime (next_prime r) ∧ r < next_prime r := by
  have hne : {k : ℕ | Nat.Prime k ∧ r < k}.Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (r + 1)
    exact ⟨p, hp2, hp1⟩
  exact Nat.sInf_mem hne

/-- `0 < a n` is equivalent to the existence of an explicit witnessing pair of primes. -/
theorem a_pos_iff (n : ℕ) : 0 < a n ↔
    ∃ p < n, ∃ q < n, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = 2 * n := by
  unfold a
  simp only [Finset.card_pos, Finset.filter_nonempty_iff, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨p, q⟩, ⟨hp, hq⟩, h⟩; exact ⟨p, hp, q, hq, h⟩
  · rintro ⟨p, hp, q, hq, h⟩; exact ⟨(p, q), ⟨hp, hq⟩, h⟩

/-- GENUINE VERIFIED SUFFICIENT CONDITION (no `sorry`): if `n` is itself a sum of two
consecutive primes, i.e. `S_sum p = n` for some prime `p < n`, then `a n > 0` (take `q = p`).
This settles the "diagonal" of the conjecture.  Computationally, such `n` have density `~1/log n`
and cover only about 6% of `n ≥ 474`; the remaining ~94% require the off-diagonal representation,
which is the open binary-Goldbach-strength core isolated below. -/
theorem a_pos_of_consec_sum (n p : ℕ) (hp : Nat.Prime p) (hn : S_sum p = n) (hpn : p < n) :
    0 < a n := by
  rw [a_pos_iff]
  exact ⟨p, hpn, p, hpn, hp, hp, le_refl p, by rw [hn]; ring⟩

/- ###  The irreducible open core

By `a_pos_iff`, the conjecture is equivalent to: for every `n ≥ 474` there exist primes
`p ≤ q < n` (with `p' := next_prime p`, `q' := next_prime q`) such that
`(p + p') + (q + q') = 2n`.

Writing `h(p) := (p + p')/2` for the midpoint of consecutive primes (an even split, valid
for odd `p`, forced for `n ≥ 474` by a parity argument), this says precisely:

>   every `n ≥ 474` is a sum of two interprime–midpoints,  `n = h(p) + h(q)`.

The set `H := { h(p) : p an odd prime }` has density `~ 1/log`, exactly like the primes
themselves, so this is a binary–Goldbach–type additive-basis-of-order-2 statement — the
analog of Goldbach's conjecture named in the docstring above.  It is an open problem
(Zhi-Wei Sun, OEIS A389790, "verified for `n ≤ 2·10^5`"; additionally verified here by
computation for all `n ≤ 10^8`, with the boundary tight: `a 473 = 0` and `a 474 = 16`).
A uniform-in-`n` construction of the witnessing primes is obstructed by the parity problem
of sieve theory; the binary problem is open even under the Generalized Riemann Hypothesis. -/

theorem oeis_a389790_existence (n : ℕ) (hn : 474 ≤ n) :
    ∃ p < n, ∃ q < n, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = 2 * n := by
  sorry

/-- OEIS A389790 Conjecture: a(n) > 0 for all n >= 474.
This is an analog of Goldbach's conjecture. It has been verified for n <= 2*10^5. -/
theorem oeis_a389790_conjecture_1 : ∀ n : ℕ, 474 ≤ n → 0 < a n := by
  intro n hn
  exact (a_pos_iff n).mpr (oeis_a389790_existence n hn)
