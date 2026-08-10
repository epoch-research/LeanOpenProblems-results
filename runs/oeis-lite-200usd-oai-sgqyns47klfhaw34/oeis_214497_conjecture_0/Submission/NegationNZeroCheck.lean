import FormalConjectures.Util.ProblemImports
open Nat

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)
abbrev BadN0 : Prop := ¬ ∃ k : ℕ, Nat.Prime ((3 ^ 0 - k) * (2 ^ 0) - 1) ∧ Nat.Prime ((3 ^ 0 - k) * (2 ^ 0) + 1)

-- n=0 failure does not imply negation because the implication hypothesis is false.
example (h0 : BadN0) : ¬ Target := by
  intro H
  -- only get a witness if we can prove 0>0, impossible
  fail_if_success exact h0 (H 0 (by omega))
  admit
