import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

lemma test_168_cases : ∀ B ⊆ ({42, 56, 84, 168} : Finset ℕ), B ≠ ∅ →
  13 - B.card ≤ 12 ∧
  (13 - B.card = 12 → B.sum id + 130 > 168) ∧
  (13 - B.card = 11 → B.sum id + 102 > 168) ∧
  (13 - B.card = 10 → B.sum id + 78 > 168) ∧
  (13 - B.card = 9 → B.sum id + 57 > 168) := by decide
