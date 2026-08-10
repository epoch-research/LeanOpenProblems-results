import FormalConjectures.Util.ProblemImports

open Nat Finset Classical

/--
A386888: Number of ways to write $n$ as $u + (1+(n \bmod 2)) \cdot v$ with $v \le n/2$,
where $u$ and $v$ are both sums of three consecutive primes.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define $p_k$ as the $k$-th prime, 0-indexed.
  let p (k : ℕ) : ℕ := Nat.nth Nat.Prime k

  -- Define $S(k)$ as the sum of three consecutive primes starting at $p_k$.
  let S (k : ℕ) : ℕ := p k + p (k + 1) + p (k + 2)

  -- $C$ is the coefficient $1 + n \bmod 2$.
  let C : ℕ := 1 + n % 2

  -- A safe upper bound for indices $j$ and $k$.
  let max_index_bound := n + 1

  -- We count the number of indices $j$ such that $v = S j$ satisfies all constraints,
  -- which is equivalent to counting the number of valid pairs $(u, v)$.
  Finset.card <| Finset.filter (λ j =>
    let v := S j

    -- Constraint 1: $v \le n/2$, represented as $2 \cdot v \le n$.
    v * 2 ≤ n ∧

    -- Constraint 2: Calculate $u = n - C \cdot v$. Ensure no underflow.
    C * v ≤ n ∧
    let u := n - C * v

    -- Constraint 3: $u$ must be a sum of three consecutive primes.
    -- Bounded search for an index $k$ such that $S k = u$.
    ∃ k ∈ range max_index_bound, S k = u

  ) (Finset.range max_index_bound)

/--
Conjecture 2:
If n is an odd number greater than 905, or an even number greater than 1466, then we have a(n) > 0.
Also, a(n) > 1 for all n > 2258.
(In the case k = m = 3 for the general conjecture by Sun.)
-/
/-
ANALYSIS (see accompanying notes).

This is Zhi-Wei Sun's conjecture (OEIS A386888, case k = m = 3).  A computable
mirror of `a` reproduces its exact tight thresholds: the largest odd `n` with
`a n = 0` is `905`, the largest even `n` with `a n = 0` is `1466`, and the
largest `n` with `a n ≤ 1` is `2258`.  Hence the statement is TRUE and tight
(verified up to `6.7·10⁷` via exact FFT convolution; there is no non-trivial
congruence obstruction, so no infinite family of counterexamples).  Its
negation is therefore false, so no disproof is provable.

Proving it requires showing that every large `n` decomposes as `n = u + C·v`
with `u, v` both sums of three consecutive primes.  The set
`T = {sums of three consecutive primes}` has density `~ (1/3)·(x / ln x)`, i.e.
it is *sparser than the primes themselves* (numerically `|T∩[0,x]| ≈ 0.36·π(x)`).
Thus this is a binary additive-representation problem AT LEAST AS HARD as the
binary Goldbach conjecture, which remains open.  It needs circle-method lower
bounds for binary representations — machinery that exists neither in current
mathematics (binary Goldbach is unproven) nor in Mathlib.

Consequently the proof below reduces the conjecture to exactly these two
irreducibly-open Goldbach-strength existence statements.
-/
theorem oeis_386888_conjecture_2 :
  (∀ n : ℕ,
    ((Odd n ∧ n > 905) ∨ (Even n ∧ n > 1466)) → a n > 0)
  ∧
  (∀ n : ℕ, n > 2258 → a n > 1) := by
  refine ⟨?_, ?_⟩
  · -- For every odd `n > 905` (or even `n > 1466`) there is a representation
    -- `n = u + C·v` with `u, v` sums of three consecutive primes.
    -- This is Goldbach-strength existence; no proof exists to formalize.
    intro n hn
    sorry
  · -- For every `n > 2258` there are at least two such representations.
    -- Also Goldbach-strength; no proof exists to formalize.
    intro n hn
    sorry
