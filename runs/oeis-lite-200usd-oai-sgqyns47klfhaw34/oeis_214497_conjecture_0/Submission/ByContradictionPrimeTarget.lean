import FormalConjectures.Util.ProblemImports
open Nat

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

example : Target := by
  refine Classical.byContradiction ?_
  intro hn
  -- Can automation prove contradiction from negated target?
  push_neg at hn
  exact?

example : Target := by
  exact Classical.byContradiction' (α := Target) ?_

example : ¬¬Target := by
  intro h
  push_neg at h
  exact?
