import FormalConjectures.Util.ProblemImports

open Nat Set

-- Attempt every heavy tactic on the core prime-gap statement.
example (n : ℕ) (hn : n > 0) :
    ∃ p, Nat.Prime p ∧ n ^ 2 < p ∧ p ≤ n ^ 2 + 1 + Nat.totient n := by
  sorry

-- Is there ANY Mathlib lemma giving a prime near a target? Search the interval form.
example (n : ℕ) (hn : 1 < n) : ∃ p, Nat.Prime p ∧ n < p ∧ p < 2 * n := by
  exact?
