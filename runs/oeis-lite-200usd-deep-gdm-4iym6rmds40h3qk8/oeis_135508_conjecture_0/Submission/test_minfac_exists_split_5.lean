import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000000
set_option maxHeartbeats 0

open Nat

lemma test_decide_1 : ∀ p, p < 2000 → 5 ≤ p → ¬ Nat.Prime (p - 2) → ∃ m ≤ 113, 2 ≤ m ∧ m ∣ p - 2 := by
  decide
