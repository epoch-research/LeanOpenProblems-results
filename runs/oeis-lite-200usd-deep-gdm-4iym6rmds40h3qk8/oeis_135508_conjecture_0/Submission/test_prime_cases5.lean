import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000000

open Nat

lemma test_interval_cases (q : ℕ) (hq : Nat.Prime q) (hq_le : q ≤ 3) : q = 2 ∨ q = 3 := by
  interval_cases q
  · contradiction
  · contradiction
  · left; rfl
  · right; rfl
