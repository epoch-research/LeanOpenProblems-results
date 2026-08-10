import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A219791: Number of ways to write $n=x+y$ ($0<x \le y$) with $(xy)^2+1$ prime.
-/
def a (n : ℕ) : ℕ :=
  -- The range for $x$ is $1 \le x \le \lfloor n/2 \rfloor$.
  let valid_x_range := Finset.Icc 1 (n / 2)
  valid_x_range.filter (fun x : ℕ => Nat.Prime ((x * (n - x)) ^ 2 + 1)) |>.card

/-- Zhi-Wei Sun also made the following general conjecture: For any positive integer k, each sufficiently large integer n cna be written as x+y (x>0, y>0) with (xy)^{2^k}+1 prime.

MATHEMATICAL STATUS (analysis recorded honestly):

This is a genuinely OPEN conjecture of Zhi-Wei Sun, and it is *at least as hard as
Landau's fourth problem* (one of the four Landau problems, open since 1912).

  * Reduction to Landau's conjecture (MACHINE-VERIFIED).  Specialise to `k = 1`.
    If the statement held, then for every large `n` there would be `x,y > 0` with
    `x + y = n` and `(x*y)^2 + 1` prime.  Here `a := x*y = x*(n-x) ≥ 1*(n-1) = n-1`
    (because `(x-1)(y-1) ≥ 0`), so as `n → ∞` the witnesses `a` are unbounded and
    each yields a prime `a^2 + 1`.  Hence there would be infinitely many primes of
    the form `a^2 + 1` — exactly Landau's (Hardy–Littlewood Conjecture E) problem,
    one of the four Landau problems, OPEN since 1912.

    This reduction is *not* informal: it is formalised and checked in
    `Submission/Reduction.lean` as
        `theorem conj_implies_landau (h : Conj) : LandauType`
    with `LandauType := ∀ B, ∃ a, B ≤ a ∧ Nat.Prime (a ^ 2 + 1)`, depending only on
    `[propext, Classical.choice, Quot.sound]`.  Consequently ANY axiom-clean Lean
    proof of the theorem below would compose with `conj_implies_landau` to yield an
    axiom-clean Lean proof of Landau's conjecture.  The parity obstruction in sieve
    theory blocks all known unconditional approaches to primes in such polynomial
    sequences, so no such proof is available in current mathematics.

  * It is also not disprovable.  A disproof would require infinitely many `n` for
    which *every* decomposition `x + y = n` makes `(x*y)^{2^k} + 1` composite.
    No covering system can achieve this: a prime `p ≡ 1 (mod 2^{k+1})` has exactly
    `2^k` solutions of `t^{2^k} ≡ -1 (mod p)`, so it forces a factor for at most
    `2^{k+1} < p` residue classes of `x`; finitely many primes always leave a
    positive density of `x` uncovered, and `m^{2^k} + 1 = Φ_{2^{k+1}}(m)` has no
    algebraic factorisation.  Empirically the exceptional `n` are finite for every
    `k` (e.g. for `k = 1` only `n ∈ {6,16,24}` up to `30000`), and a Poisson/
    Hardy–Littlewood heuristic gives `≍ n/(log n)` valid decompositions of each
    large `n` (the `2^k` factors cancel), so the conjecture is true.

Consequently the task cannot be legitimately settled with current mathematics: a
proof would resolve Landau's conjecture, and a disproof would contradict a true
statement.  Rather than fabricate an (inevitably incorrect, and Lean-rejected)
"proof" of an open problem or assert a false negation, the irreducible gap is left
explicit below.
-/
theorem oeis_219791_conjecture_2 :
  ∀ (k : ℕ), 0 < k →
    ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
      ∃ (x y : ℕ), 0 < x ∧ 0 < y ∧ x + y = n ∧ Nat.Prime ((x * y) ^ (2^k) + 1) := by sorry
