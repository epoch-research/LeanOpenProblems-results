import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

lemma test_120_cases : ∀ B ⊆ ({30, 40, 60, 120} : Finset ℕ), B ≠ ∅ →
  13 - B.card ≤ 12 ∧
  (13 - B.card = 12 → B.sum id + 110 > 120) ∧
  (13 - B.card = 11 → B.sum id + 86 > 120) ∧
  (13 - B.card = 10 → B.sum id + 66 > 120) ∧
  (13 - B.card = 9 → B.sum id + 51 > 120) := by decide
