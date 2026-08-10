import FormalConjectures.Util.ProblemImports

open Lean Elab Tactic Meta

set_option maxHeartbeats 100000000
set_option maxRecDepth 20000000

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

theorem oeis_374605_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := by
  intro n hn1 hn2
  -- Can we write an inline custom tactic?
  -- Wait, inline elab requires top-level elab definition.
  sorry







