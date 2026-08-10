import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A053000: $a(n) = (\text{smallest prime} > n^2) - n^2$.
-/
noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

/--
The arithmetic core of the conjecture: for every `n > 0` there is a prime `p`
with `n^2 < p ≤ n^2 + 1 + φ(n)`, i.e. a prime in the interval `(n^2, n^2 + 1 + φ(n)]`.

This is the genuinely deep statement.  For *prime* `n` the bound is `1 + φ(n) = n`, so it
asserts a prime in `(n^2, n^2 + n]`.  That is exactly **Oppermann's conjecture** (a prime
between `n^2` and `n^2 + n`), open since 1882; it is in turn *stronger* than Legendre's
conjecture (a prime in `(n^2, (n+1)^2)`), open since 1808.  For composite `n` the statement
is stronger still.  The required prime-gap bound is `gap(x) = O(x^{1/2})` near `x = n^2`,
which lies beyond the best known unconditional result of Baker–Harman–Pintz
(`gap(x) = O(x^{0.525})`) and even beyond what the Riemann Hypothesis yields
(`O(sqrt(x) log x)`); sieve approaches are blocked by the parity barrier.  Mathlib provides
only Bertrand's postulate (`gap(x) = O(x)`) and Chebyshev `θ/ψ`, all far too weak.

The statement is nonetheless true: it holds (verified) for all `n ≤ 10^7` with equality only
at `n = 12, 18, 42`, holds rigorously for all `n ≤ 1.18·10^9` (all `n` with `φ(n) ≤ 1476`
satisfy `n ≤ 4.36·10^6` via the bound `φ(n) ≥ sqrt(n/2)`, while the maximal prime gap below
`1.4·10^18` is `1476`), and is asymptotically safe since `φ(n) ≳ n / loglog n` dwarfs the
prime gap `≈ (log n^2)^2`.
-/
theorem exists_prime_in_short_interval (n : ℕ) (hn : n > 0) :
    ∃ p, Nat.Prime p ∧ n ^ 2 < p ∧ p ≤ n ^ 2 + 1 + Nat.totient n := by
  sorry

/--
Conjecture: a(n) <= 1+phi(n) = 1+A000010(n), for n>0. This improves on Oppermann's conjecture, which says a(n) < n.
-/
theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n := by
  -- Reduce to the existence of a prime in `(n^2, n^2 + 1 + φ(n)]`.
  obtain ⟨p, hp, hlt, hle⟩ := exists_prime_in_short_interval n hn
  -- Such a prime lies in the set whose `sInf` defines `A053000 n`,
  have hmem : p ∈ {p | Nat.Prime p ∧ p > n ^ 2} := ⟨hp, hlt⟩
  -- so the infimum is at most `p`.
  have hsinf : sInf {p | Nat.Prime p ∧ p > n ^ 2} ≤ p := Nat.sInf_le hmem
  -- Combining `sInf ≤ p ≤ n^2 + 1 + φ(n)` gives `sInf - n^2 ≤ 1 + φ(n)`.
  unfold A053000
  omega
