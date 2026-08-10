import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000000

open Nat

lemma test_decide : ∀ p < 13591, Nat.Prime p → ¬ Nat.Prime (p - 2) → ∃ m ≤ 103, 2 ≤ m ∧ m ∣ p - 2 := by
  decide
