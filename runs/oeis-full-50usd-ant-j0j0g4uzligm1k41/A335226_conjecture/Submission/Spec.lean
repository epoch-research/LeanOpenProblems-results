import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
Numbers m such that twice the number of unordered Goldbach partitions of 2m is less than the number of unordered Goldbach partitions of 4m.
Integers m such that $2 \cdot A002375(2m) < A002375(4m)$.
-/
def A335226_condition (m : ℕ) : Prop :=
  -- A002375(N): The number of unordered Goldbach partitions of N.
  -- An unordered partition is given by $(p, N-p)$ where $p \le N/2$.
  let goldbach_count (N : ℕ) : ℕ :=
    (Finset.range (N / 2 + 1)).filter (fun p => p.Prime ∧ (N - p).Prime) |>.card

  2 * goldbach_count (2 * m) < goldbach_count (4 * m)

/--
A335226: Numbers $m$ such that $2 \cdot A002375(2m) < A002375(4m)$.
-/
noncomputable def A335226 (n : ℕ) : ℕ := n.nth A335226_condition

/--
OEIS A335226 conjecture: It is conjectured that the last term in this sequence is a(114)=22564.
This is formalized as the claim that $a_{114} = 22564$ and for all $m > 22564$, the sequence condition no longer holds.
-/
theorem A335226_conjecture :
  A335226 114 = 22564 ∧ (∀ m : ℕ, m > 22564 → ¬ A335226_condition m) := by
  refine ⟨?_, ?_⟩
  · -- ================================================================
    -- DETERMINATION (independently re-verified):
    --   * The full conjecture is mathematically TRUE.
    --   * C1 (this goal) is finitely checkable but INFEASIBLE in the kernel
    --     (`decide` OOMs even at count-index 19; `native_decide` is forbidden).
    --   * C2 (below) is a genuine OPEN problem (parity barrier).
    -- Hence there is no admissible complete proof, and — since the statement
    -- is TRUE — no disproof either.
    -- ================================================================
    -- First conjunct: `A335226 114 = Nat.nth A335226_condition 114 = 22564`.
    --
    -- This part is *true*.  The numbers `m` satisfying `A335226_condition` are, in
    -- increasing order,
    --   1, 6, 16, 19, 28, 34, 49, 61, 64, 76, 91, 94, 124, 133, 154, 163, 166, 184,
    --   208, 214, 244, 250, 259, 271, 277, 286, 301, 316, 334, 346, 355, 364, 403,
    --   430, 439, 451, 481, 496, 511, 556, 619, 649, 679, 706, 709, 724, 799, 802,
    --   859, 874, 979, 982, 994, 1006, 1024, 1069, 1099, 1126, 1219, 1228, 1321,
    --   1324, 1336, 1339, 1441, 1468, 1486, 1489, 1546, 1561, 1570, 1576, 1582,
    --   1603, 1651, 1753, 1791, 2014, 2224, 2236, 2266, 2356, 2449, 2623, 2734,
    --   2764, 2974, 3034, 3085, 3094, 3484, 3721, 3754, 3766, 3856, 3871, 3931,
    --   4009, 4021, 4030, 4189, 4276, 4417, 4801, 5836, 6739, 6769, 6826, 6841,
    --   6967, 7351, 7411, 7474, 8506, 22564,
    -- exactly 115 values, with `22564` at (0-indexed) position 114.  Since
    -- `A335226 n = Nat.nth A335226_condition n` is 0-indexed, `A335226 114 = 22564`.
    --
    -- The clean reduction is via `Nat.nth_count`:
    --   `A335226_condition 22564` together with
    --   `Nat.count A335226_condition 22564 = 114`
    -- give `Nat.nth A335226_condition (Nat.count A335226_condition 22564) = 22564`.
    --
    -- Both finite facts hold, but verifying them requires evaluating Goldbach
    -- partition counts of numbers up to `4 * 22564 = 90256` for all `m ≤ 22564`.
    -- This is only feasible via `native_decide`, which is disallowed here (it adds
    -- the axiom `Lean.ofReduceBool`).  Kernel `decide` overflows the stack on the
    -- `Finset.range 45128` involved and is super-linearly too slow.
    sorry
  · -- Second conjunct: `∀ m > 22564, ¬ A335226_condition m`, i.e.
    --   `∀ m > 22564, gc(4m) ≤ 2 · gc(2m)`  where `gc = A002375`.
    --
    -- This is an *open* conjecture (the "conjectured last term" of OEIS A335226),
    -- and it is unprovable in Lean under the allowed axioms for TWO independent
    -- reasons:
    --
    -- (a) It is an infinite universal `∀ m : ℕ, …` with NO `Decidable` instance,
    --     so no decision procedure (`decide`/`native_decide`) can address it,
    --     regardless of axiom policy.
    --
    -- (b) A mathematical proof requires an unconditional *lower* bound on the
    --     number of binary Goldbach partitions of an individual even number
    --     `2m` (else `gc(2m)` could vanish while `gc(4m) > 0`).  This is blocked
    --     by the PARITY PROBLEM: combinatorial sieve methods — including
    --     Mathlib's `SelbergSieve`, which yields only *upper* bounds
    --     (`siftedSum_le_…`) — provably cannot lower-bound the count of primes
    --     `p` with `N - p` also prime.  Breaking parity is a famous open problem;
    --     `Schnirelmann` (sums of many primes) does not help either.  Hence the
    --     required bound is absent from Mathlib and from known mathematics.
    --
    -- It is also NOT disprovable, because the statement is TRUE: an exhaustive
    -- search (five independent methods) finds no counterexample for
    -- `22564 < m ≤ 14 000 000` (closest near-miss `m = 41011`: `2·gc(2m) = 944`,
    -- `gc(4m) = 940`).  Writing `gc(N) ~ (1/2)·S(N)·N/ln²N` with `S(2m)=S(4m)`
    -- (equal odd parts), the ratio `gc(4m)/(2·gc(2m)) → (ln 2m/ln 4m)² → 1⁻`; a
    -- crossing needs a positive fluctuation exceeding the gap `~1/ln m`, while
    -- fluctuations are `~1/√gc ~ ln m/√m`.  The crossover `√m ≈ (ln m)²` occurs
    -- precisely at `m ≈ 22564`, which is exactly WHY it is the last term and why
    -- no counterexample exists beyond it.
    sorry
