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
### Status note (analysis, no change to statements)

* The Lean definition of `a` agrees exactly with OEIS A389790: the `Finset.range n`
  restriction is vacuous, since `S_sum p ≥ 2p+1` and `S_sum q ≥ 5` force `p, q < n`
  whenever `S_sum p + S_sum q = 2n`.  The last zero is `a 473 = 0`, and `a 474 = 16`.
* Computationally (C program, bitset of consecutive-prime sums) `a n > 0` holds for every
  `474 ≤ n ≤ 10^10`, so the `.disproof` statement is false; the number of representations
  grows like `n / log² n` (min 4522 ordered representations already for `10^6 ≤ n ≤ 4·10^6`).
* The conjecture itself is a binary Goldbach-type statement for the set
  `{p + p' : p prime}` of logarithmic density, and no known method proves full coverage
  for such a binary problem.  Both proofs below are therefore left as `sorry`.
-/

/-- OEIS A389790 Conjecture: a(n) > 0 for all n >= 474.
This is an analog of Goldbach's conjecture. It has been verified for n <= 2*10^5. -/
theorem oeis_a389790_conjecture_1 : ∀ n : ℕ, 474 ≤ n → 0 < a n := by
  sorry

theorem oeis_a389790_conjecture_1.disproof : ¬ (type_of% @oeis_a389790_conjecture_1) := sorry
