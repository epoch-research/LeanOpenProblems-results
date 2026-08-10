import FormalConjectures.Util.ProblemImports
open Set

/--
A159829: $a(n)$ is the smallest natural number $m$ such that $n^3+m^3+1^3$ is prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | 1 ≤ m ∧ Nat.Prime (n ^ 3 + m ^ 3 + 1) }

/--
OEIS A159829 Exponent k>2: Are there infinitely many primes of the forms $n^k+m^k$ and $n^k+m^k+1^k$?
We formalize the claim for $n^k+m^k+1^k$, which generalizes the sequence A159829.
-/
theorem oeis_159829_conjecture_0 : ∀ (k : ℕ), k ≥ 3 →
    Set.Infinite { p : ℕ | ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ Nat.Prime p ∧ p = n ^ k + m ^ k + 1 } := by
  sorry
