import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A343812: $a(n) = \sum_{i \le n} (A007504(n) \bmod \mathrm{prime}(i))$.
$A007504(n)$ is the sum of the first $n$ primes, and $\mathrm{prime}(i)$ is the $i$-th prime.
The index $i$ runs from $1$ to $n$, which corresponds to $k=0$ to $n-1$ in 0-indexing.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- A007504(n), the sum of the first n primes.
  let S_n : ℕ := (range n).sum (fun k => Nat.nth Nat.Prime k)

  -- The result is the sum of S_n modulo the first n primes.
  (range n).sum (fun i => S_n % (Nat.nth Nat.Prime i))

/-- A343812 Does any term occur more than once? (Conjectured to be "no" for $n \ge 1$). -/
theorem A343812_conjecture (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : a m = a n → m = n := by
  sorry
