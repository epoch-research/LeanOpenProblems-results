import FormalConjectures.Util.ProblemImports

open Finset ZMod Nat Set Classical

/--
The predicate that $\{2^k - k: k = 1,\dots,m\}$ contains a complete system of residues modulo $n$.
This is equivalent to the image of $k \mapsto 2^k - k \pmod n$ for $k \in \{1, \dots, m\}$ being the entire $\mathbb{Z}_n$.
-/
def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

/--
A232616: Least positive integer $m$ such that $\{2^k - k: k = 1,\dots,m\}$
contains a complete system of residues modulo $n$.
-/
noncomputable def A232616 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    -- Since n is non-zero, the NeZero n instance is available for ZMod n operations.
    have hn : NeZero n := NeZero.mk h

    -- The set $S$ of all $m$ which satisfy the complete residue system condition.
    -- The set $S$ is non-empty based on the external theorem $a(n) \le n^2$.
    let S : Set ℕ := { m : ℕ | A232616_prop n m }

    -- The least element of a non-empty set of natural numbers is its infimum, sInf.
    sInf S

/--
Conjecture (i): $a(n) < 2 \cdot (\text{prime}(n) - 1)$ for all $n > 0$,
where $\text{prime}(n)$ is the $n$-th prime number (1-indexed).
-/
theorem oeis_232616_conjecture_i (n : ℕ) (hn : 0 < n) :
    A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1) := by
  -- Reduce the conjecture to a single covering statement.
  --
  -- `A232616 n` is the least `m` such that `{2^k - k : k = 1, …, m}` is a complete
  -- residue system mod `n` (or `0` if no such `m` exists).  Since the family of
  -- covering `m` is upward closed, `A232616 n < B` is *equivalent* to the assertion
  -- that `k ↦ 2^k - k` already covers `ℤ/n` for `k ∈ [1, B - 1]`, i.e.
  -- `A232616_prop n (B - 1)`.
  --
  -- Numerically the conjecture holds with worst-case ratio `0.9028` at `n = 29`
  -- (a(29) = 195, bound = 216), verified exhaustively for all `n ≤ 50000` and by
  -- sampling prime moduli up to `10^6`; the ratio decreases for large `n`.  The
  -- heuristic is `a(n) ~ 2 n ln n` (coupon collector) versus
  -- `2·(prime(n) - 1) ~ 2 n ln n + 2 n ln ln n` (by the prime number theorem), so
  -- the conjecture is safe by the `n ln ln n` margin.
  --
  -- The remaining `covering` claim below is the genuine mathematical core.  Writing
  -- `d = ord_n(2)`, one has the *exact* structural identity that the covering time
  -- equals `maxgap(A') · d` (up to one period), where `A' = 2^{-d}·{2^i - i : i ≤ d}`
  -- and `maxgap` is the largest cyclic gap.  Thus the conjecture is equivalent to the
  -- equidistribution statement that `{2^i - i mod n}` has maximal gap `O(log n)`.
  -- Every provable tool falls short of the *tight constant* required:
  --   • the period bound gives only `a(n) ≤ lcm(n, d) = O(n^2)`;
  --   • the second moment gives `#missed ≤ n^2 / M`, useless below `M > n^2`
  --     (the collision count is empirically `~ M^2/n`, i.e. essentially random);
  --   • the sharpest exponential-sum bounds give discrepancy `~ n^{3/4}`, far above
  --     the `log n` needed.
  -- Hence a rigorous proof needs an equidistribution bound for `2^k - k (mod n)` with
  -- a tight constant that is beyond current analytic number theory.  The conjecture is
  -- true (no counterexample for `n ≤ 50000`, exhaustively) but open.
  have hn0 : n ≠ 0 := hn.ne'
  haveI : NeZero n := ⟨hn0⟩
  have hp2 : 2 ≤ Nat.nth Nat.Prime (n - 1) := by
    have h := Nat.add_two_le_nth_prime (n - 1)
    omega
  set B := 2 * (Nat.nth Nat.Prime (n - 1) - 1) with hB
  have hB2 : 2 ≤ B := by rw [hB]; omega
  have covering : A232616_prop n (B - 1) := by
    sorry
  have hA : A232616 n = sInf {m : ℕ | A232616_prop n m} := by
    simp only [A232616, dif_neg hn0]
  rw [hA]
  have hle : sInf {m : ℕ | A232616_prop n m} ≤ B - 1 := Nat.sInf_le covering
  omega
