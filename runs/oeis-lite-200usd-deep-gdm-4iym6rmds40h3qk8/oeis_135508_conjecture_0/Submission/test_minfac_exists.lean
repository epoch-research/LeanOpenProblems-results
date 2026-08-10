import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000000

open Nat

lemma test_decide_exists : ∀ p, p < 13591 → ¬ Nat.Prime (p - 2) → ∃ m, 2 ≤ m ∧ m ≤ 103 ∧ m ∣ p - 2 := by
  decide
