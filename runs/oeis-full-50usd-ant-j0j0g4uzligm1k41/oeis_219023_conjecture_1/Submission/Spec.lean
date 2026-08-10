import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A219023: Number of primes $p<n$ such that $n^2-n+p$ and $n^2+n-p$ are both prime.
-/
def a (n : ℕ) : ℕ :=
  (Nat.primesBelow n).sum (fun p =>
    if (n ^ 2 - n + p).Prime ∧ (n ^ 2 + n - p).Prime then 1 else 0
  )

theorem oeis_219023_conjecture_1 (n : ℕ) (h : n > 2732) : a n > 0 := by
  sorry
