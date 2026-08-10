import FormalConjectures.Util.ProblemImports
open Nat

abbrev TargetAt (n : ℕ) : Prop := ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)
abbrev Target : Prop := ∀ n : ℕ, n > 0 → TargetAt n

example (n : ℕ) : TargetAt n = True := by
  -- should fail unless propext can prove proposition
  exact?

example : Target = True := by
  exact?

example (n : ℕ) : TargetAt n := by
  change True
  trivial
