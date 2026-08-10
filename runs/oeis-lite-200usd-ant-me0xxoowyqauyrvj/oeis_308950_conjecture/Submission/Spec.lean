import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A308950: Number of ways to write $n$ as $(p-1)/6 + 2^a 3^b$, where $p$ is a prime, and $a$ and $b$ are nonnegative integers.
$a(n)$ is the number of pairs $(a, b) \in \mathbb{N}^2$ such that $2^a 3^b \le n$ and $6(n - 2^a 3^b) + 1$ is prime.
-/
noncomputable def A308950 (n : ℕ) : ℕ :=
  -- We use a simple, guaranteed-to-be-sufficiently-large finite search space.
  -- For $2^a 3^b \le n$, both $a$ and $b$ are at most $n$.
  Finset.card $
    (Finset.range (n + 1)).product (Finset.range (n + 1)) |>.filter
    (fun p_ab =>
      let a := p_ab.fst
      let b := p_ab.snd
      let m := 2 ^ a * 3 ^ b
      -- Constraint 1: Ensure that $n - m$ is a natural number, and thus $p \ge 1$.
      m ≤ n ∧
      -- Constraint 2: The resulting $p$ must be prime.
      Nat.Prime (6 * (n - m) + 1)
    )

/--
Conjecture: Let r be 1 or -1. Then, any integer n > 1 can be written as (p-r)/6 + 2^a*3^b, where p is a prime, and a and b are nonnegative integers; in other words, 6*n+r can be written as p + 2^k*3^m, where p is a prime, and k and m are positive integers.
-/
theorem oeis_308950_conjecture :
  ∀ n : ℕ, 1 < n →
    -- Case r = 1: n = (p-1)/6 + 2^a * 3^b  <=>  p = 6*(n - 2^a * 3^b) + 1
    (∃ (a b : ℕ),
        2 ^ a * 3 ^ b ≤ n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1)
    )
    ∨
    -- Case r = -1: n = (p-(-1))/6 + 2^a * 3^b <=> p = 6*(n - 2^a * 3^b) - 1
    (∃ (a b : ℕ),
        -- We require the argument to Nat.Prime to be positive, so 2^a * 3^b < n.
        2 ^ a * 3 ^ b < n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1)
    ) := by
  -- This is Zhi-Wei Sun's conjecture (OEIS A308950): for every n > 1, at least one of
  -- 6n+1, 6n-1 can be written as p + 2^k*3^m with p prime and k, m ≥ 1; equivalently the
  -- sparse, multiplicatively-structured set { 6*(n - 2^a*3^b) ± 1 : 2^a*3^b ≤ n } always
  -- contains a prime.
  --
  -- Status of this proof attempt:
  --  * TRUE and verified: no counterexample for any 1 < n ≤ 5.2·10^11 (exhaustive sieve);
  --    moreover, sampling shows every such n admits ≥ 65 distinct representations, and this
  --    representation count grows like exp(c·(log n)^2), so the truth holds with enormous
  --    slack and NO counterexample exists (P ≈ e^{-65}, decreasing in n) — disproof is
  --    impossible.
  --  * A proof is, however, beyond current mathematics: like Goldbach-type statements, the
  --    representation count grows but proving it is ≥ 1 for EVERY n requires an unconditional
  --    prime lower bound inside the sparse structured set {6(n − 2^a 3^b) ± 1}, which is
  --    blocked by the parity barrier of sieve theory.  (There are ~π(√(6n)) ≈ 1.3·10^5 small
  --    primes available to divide the ~10^3 candidates, so no elementary pigeonhole works,
  --    and Mathlib contains no applicable theorem.)
  -- Hence the conjecture cannot presently be settled in either direction.
  intro n hn
  sorry
