import FormalConjectures.Util.ProblemImports
open Nat Finset
open scoped Nat.Prime
set_option maxRecDepth 500000
set_option maxHeartbeats 0

/--
A237720: Number of primes $p \le \lfloor (n+1)/2 \rfloor$ with \\lfloor \sqrt{n-p} \\rfloor prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ =>
    p.Prime ∧
    2 * p ≤ n + 1 ∧
    (Nat.sqrt (n - p)).Prime
  ) (Finset.range (n + 1)))

theorem oeis_A237720_conjecture_ii (n : ℕ) (hn : n > 2) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := sorry
