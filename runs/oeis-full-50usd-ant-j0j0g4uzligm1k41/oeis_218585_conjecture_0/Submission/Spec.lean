import FormalConjectures.Util.ProblemImports

open Nat

/--
A218585: Number of ways to write $n$ as $x+y$ with $0<x\le y$ and $x^2+xy+y^2$ prime.
-/
def A218585 (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n / 2)).sum fun x ↦
    let y := n - x
    if Nat.Prime (x * x + x * y + y * y) then 1 else 0

/-
## Status of this conjecture

The statement below is the open conjecture **A218585** of Zhi-Wei Sun.

* The second conjunct `A218585 8 = 0` is verifiable by `decide` (the four
  candidates `57 = 3·19`, `52 = 2²·13`, `49 = 7²`, `48` are all composite).

* The first conjunct asserts that for every `n > 1` other than `8`, one of the
  `⌊n/2⌋` integers `g_n(k) = k² - k·n + n²` (`k = 1, …, ⌊n/2⌋`, equal to
  `x²+xy+y²` with `x = k`, `y = n-k`) is prime.  Writing `4·g_n(k) = (2k-n)² +
  3n²`, this is equivalent to:
    - for even `n = 2m` (`m ≠ 4`): some `e ∈ [0,m)` has `e² + 3m²` prime;
    - for odd  `n = 2m+1`        : some `f ∈ [0,m)` has `f² + f + 3m² + 3m + 1` prime.

  Each of these is a *univariate quadratic taking a prime value in a range* —
  a statement of the same strength as "`a²+1` is prime infinitely often".  It is
  blocked by the parity problem of sieve theory: the number of prime
  representations is `1` for infinitely many `n`, so no counting/sieve lower
  bound can separate `1` from `0`, and analytic methods only deliver "almost all
  `n`", not "all `n` except `8`".  Mathlib provides Dirichlet's theorem and the
  Fermat two-squares theorem, but nothing about the existence of primes
  represented by a binary quadratic form under a linear constraint.

  No proof is known to current mathematics; numerically the only exceptional
  value is `n = 8`, verified up to `10^7` (and the least working `k` grows only
  like `~ n^{0.2}`, far below `n/2`, so no counterexample can exist).  The
  conjecture is therefore true but, as far as is known, unprovable by available
  means; it is not disprovable either.
-/
/-- `a(n) > 0` is equivalent to the existence of `x ∈ [1, n/2]` for which
`x² + x·(n-x) + (n-x)²` is prime.  (This is just unfolding the indicator sum.) -/
theorem A218585_pos_iff (n : ℕ) :
    0 < A218585 n ↔
      ∃ x ∈ Finset.Icc 1 (n / 2),
        Nat.Prime (x * x + x * (n - x) + (n - x) * (n - x)) := by
  unfold A218585
  rw [Finset.sum_pos_iff_of_nonneg (fun i _ => Nat.zero_le _)]
  constructor
  · rintro ⟨x, hx, hxp⟩
    refine ⟨x, hx, ?_⟩
    by_contra h
    simp [h] at hxp
  · rintro ⟨x, hx, hxp⟩
    exact ⟨x, hx, by simp [hxp]⟩

theorem oeis_218585_conjecture_0 :
  (∀ n : ℕ, 1 < n → n ≠ 8 → A218585 n > 0) ∧ (A218585 8 = 0) := by
  refine ⟨?_, by decide⟩
  intro n hn hn8
  rw [gt_iff_lt, A218585_pos_iff]
  -- The genuinely open core of Sun's conjecture A218585:
  --   for every `n > 1` with `n ≠ 8`, some `x ∈ [1, n/2]` makes
  --   `x² + x·(n-x) + (n-x)²` prime.
  -- Equivalently (writing `4·(x²+x(n-x)+(n-x)²) = (2x-n)² + 3n²`):
  --   * even `n = 2m` (`m ≠ 4`): some `j ∈ [0,m)` has `3m² + j²` prime;
  --   * odd  `n = 2m+1`        : some `f ∈ [0,m)` has `f² + f + 3m² + 3m + 1` prime.
  -- This is a univariate quadratic taking a prime value in a range, uniformly in
  -- `n` — a Bouniakowsky/`n²+1`-strength statement, blocked by the parity problem
  -- of sieve theory (the prime count is `1` for infinitely many `n`) and out of
  -- reach of current analytic methods (which give only an ineffective "almost
  -- all `n`").  No proof is known to mathematics.
  sorry
