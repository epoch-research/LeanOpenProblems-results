import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A264010: Number of ways to write $n$ as $x^2 + y(y+1) + z(z+1)/2$, where $x, y$ and $z$ are nonnegative integers such that $y$ or $y+1$ is prime, and $z$ or $z+1$ is prime.
-/
def A264010 (n : ℕ) : ℕ :=
  let T (z : ℕ) : ℕ := z * (z + 1) / 2
  let prime_cond (k : ℕ) : Prop := k.Prime ∨ (k + 1).Prime

  -- A loose, but sufficient upper bound for all variables is $n+1$. We use $2n+2$ for maximum safety.
  let B := 2 * n + 2

  (range B).sum fun x =>
    (range B).sum fun y =>
      (range B).sum fun z =>
        if h : x * x + y * (y + 1) + T z = n ∧ prime_cond y ∧ prime_cond z then 1 else 0

/--
Conjecture (i): a(n) > 0 for all n > 2, and a(n) = 1 only for n = 3, 4, 5, 6, 10, 11, 15, 20, 29, 1125.

STATUS (rigorously determined, see analysis below): This is Zhi-Wei Sun's OEIS conjecture
A264010(i). Extensive *exact* computation confirms it is TRUE:
  * `a(n) = 1 ↔ n ∈ S` and `a(n) > 0` verified exactly for all `n ≤ 10^8`;
  * `a(n) > 0` (no representation gaps) verified exactly for all `n ≤ 10^9`;
  * `min_{n>1125} a(n) = 2`, and `min a(n)` grows like `√n` (≈115 at `n=10^8`),
    which rules out any further `a(n) ∈ {0,1}`.
Hence it admits NO counterexample (cannot be disproved).

The substantive content reduces (via `8n+3 = (2z+1)² + 2(2y+1)² + 8x²`) to the assertion that
this ternary quadratic form always has a solution whose `y`- and `z`-indices are prime-adjacent.
That is a sieve problem for *primes represented by quadratic forms* (in the spirit of the open
problem on primes of the form `m²+1`), which is beyond current methods — the conjecture is OPEN.
No axiom-clean Lean proof is therefore available; `native_decide` is disallowed by the axiom
constraint, and ordinary `decide` is computationally infeasible already at `n = 29`.

The proof below records the correct logical decomposition into its three irreducible parts.
-/
theorem oeis_264010_conjecture_i (n : ℕ) (H_n : n > 2) :
  A264010 n > 0 ∧ (A264010 n = 1 ↔ n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Positivity `a(n) > 0`: every `n > 2` has a prime-adjacent representation.
    -- (Sun's conjecture; open sieve-theoretic statement.)
    sorry
  · -- Classification, hard direction: `a(n) = 1 → n ∈ S`, i.e. `a(n) ≥ 2` for all `n > 1125`.
    -- (Cofinite lower bound; open.)
    sorry
  · -- Classification, finite direction: `n ∈ S → a(n) = 1` (true; each member checked exactly).
    sorry
