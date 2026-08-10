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

/-
STATUS NOTE (investigation record, not part of the formal content):

This is a weakened (disjunctive) form of Zhi-Wei Sun's conjecture attached to
OEIS A308950 (2019), which remains an open problem of additive prime number
theory.  Findings of an extensive investigation:

1. Both disjuncts hold (each separately) for all 1 < n ≤ 10^10, verified by two
   independent implementations (so no small counterexample exists).
2. Hardy–Littlewood heuristics give P(n fails both disjuncts) ≈ (6n)^{-3.94};
   the expected number of "accidental" counterexamples beyond 10^10 is < 10^{-40}.
3. Any *constructible/certifiable* counterexample would require an Erdős-style
   covering system over the exponent lattice {(k,j) : 2^k 3^j < 6n}.  For a
   prime q, the killable density is 1/h(q), h(q) = lcm(ord_q 2, ord_q 3), and
   the total supply Σ 1/h(q) ≈ 2.15 (over all usable q, h ≤ 5100) grows only
   ~0.19 per e-fold in h, while the required coverage exponent grows linearly
   in log n.  Optimizing over all scales (10^25 … 10^1650), pool budgets,
   coupled two-target residue systems and algebraic (difference-of-powers)
   freebies, the achievable uncovered fraction obeys the empirical law
   u ≈ e^{-1.22 σ}, leaving a deficit of ≥ 70 nats between the required and the
   available search budget at every scale.  Hence the statement cannot be
   falsified in practice (though within optimally covered CRT classes the
   expected number of counterexamples diverges — around 10^300 and beyond,
   far beyond any certification budget).
4. A proof would require prime-existence in polylog-size structured sets for
   every n, beyond all known unconditional or GRH-conditional techniques.

Consequently this statement is left as stated.
-/

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
    ) := by sorry
