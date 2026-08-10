import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

lemma test_144_cases : ∀ B ⊆ ({48, 72, 144} : Finset ℕ), B ≠ ∅ →
  13 - B.card ≤ 12 ∧
  (13 - B.card = 12 → B.sum id + 139 > 144) ∧
  (13 - B.card = 11 → B.sum id + 103 > 144) ∧
  (13 - B.card = 10 → B.sum id + 79 > 144) ∧
  (13 - B.card = 9 → B.sum id + 61 > 144) := by decide
