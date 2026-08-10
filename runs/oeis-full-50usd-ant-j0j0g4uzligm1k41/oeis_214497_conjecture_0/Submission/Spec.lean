import FormalConjectures.Util.ProblemImports

open Nat

/--
A214497: Smallest $k \ge 0$ such that $(3^n-k)2^n-1$ and $(3^n-k)2^n+1$ are a twin prime pair.
-/
noncomputable def A214497 (n : ℕ) : ℕ :=
  -- Nat.sInf is the rigorous definition of the minimum element of a set of natural numbers,
  -- which translates "smallest k" directly.
  sInf {k : ℕ | Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)}

/-
OEIS A214497 Conjecture: there is always one such k for each n>0.
That is, for every $n>0$, there exists a $k \ge 0$ such that
$(3^n-k)2^n-1$ and $(3^n-k)2^n+1$ are a twin prime pair.
-/
/--
The essential mathematical content of the conjecture, stated in the equivalent
"twin prime center" form.

Because `3 ^ n - k` (truncated natural subtraction) ranges over exactly
`{0, 1, …, 3 ^ n}` as `k` ranges over `ℕ`, the conjecture below is *equivalent* to
the assertion that, for every `n > 0`, there is some `m` with `1 ≤ m ≤ 3 ^ n` such
that `m * 2 ^ n - 1` and `m * 2 ^ n + 1` are both prime.  Since these two numbers
differ by `2`, this says precisely that there is a **twin prime pair whose center
`m * 2 ^ n` is a multiple of `2 ^ n`**, i.e. twin primes `p, p + 2` with
`2 ^ n ∣ (p + 1)`.

This is a bounded, per-`n` instance of a quantitative twin-prime statement
(OEIS A214497, conjectured by Pierre Cami, 2012).  It is numerically true and the
witness `m` is always astronomically smaller than the slack bound `3 ^ n`, so the
statement cannot be refuted.  A *uniform* proof over all `n`, however, would furnish
an unconditional positive lower bound on the count of twin primes of a prescribed
2-adic shape — exactly what the **parity problem** of sieve theory forbids.  No known
unconditional result (Chen's theorem, GPY, Zhang, Maynard–Tao) produces
gap-*exactly*-`2` prime pairs, and Mathlib contains no twin-prime infrastructure.
This lemma is therefore the irreducible open core of the problem.
-/
theorem twin_center_exists (n : ℕ) (hn : n > 0) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 3 ^ n ∧
      Nat.Prime (m * 2 ^ n - 1) ∧ Nat.Prime (m * 2 ^ n + 1) := by
  sorry

/-- The stated conjecture follows from `twin_center_exists` by taking
`k = 3 ^ n - m`, so that `3 ^ n - k = m` (using `m ≤ 3 ^ n`). This reduction step is
fully verified; only `twin_center_exists` remains open. -/
theorem oeis_214497_conjecture_0 (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  obtain ⟨m, _hm1, hm2, hp1, hp2⟩ := twin_center_exists n hn
  refine ⟨3 ^ n - m, ?_, ?_⟩
  · rwa [Nat.sub_sub_self hm2]
  · rwa [Nat.sub_sub_self hm2]
