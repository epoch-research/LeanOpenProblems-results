import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A119591: Least $k \ge 1$ such that $2 \cdot n^k - 1$ is prime.
The sequence starts at $n=2$, so we return 0 for $n < 2$.
-/
noncomputable def A119591 (n : ℕ) : ℕ :=
  if h : n ≥ 2 then
    -- The minimum element of the set of positive integers k for which 2 * n^k - 1 is prime.
    let S : Set ℕ := {k : ℕ | 0 < k ∧ Nat.Prime (2 * n ^ k - 1)}
    sInf S
  else
    0

/-- OEIS A119591 Conjecture: a(n) is defined for all n. -/
theorem oeis_119591_conjecture_0 :
  ∀ n : ℕ, n ≥ 2 → ∃ k : ℕ, 0 < k ∧ Nat.Prime (2 * n ^ k - 1) :=
by sorry
