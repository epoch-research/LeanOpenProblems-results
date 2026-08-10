import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000000

open Nat

lemma test_decide_1 : ∀ p, p < 2000 → Nat.Prime p → ¬ Nat.Prime (p - 2) → ∃ m ≤ 103, 2 ≤ m ∧ m ∣ p - 2 := by
  decide

lemma test_decide_2 : ∀ p, 2000 ≤ p ∧ p < 4000 → Nat.Prime p → ¬ Nat.Prime (p - 2) → ∃ m ≤ 103, 2 ≤ m ∧ m ∣ p - 2 := by
  decide
