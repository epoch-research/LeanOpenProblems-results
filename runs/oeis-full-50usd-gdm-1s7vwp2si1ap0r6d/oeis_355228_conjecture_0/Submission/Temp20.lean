import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

lemma small_sums_120 : ∀ A ⊆ ({1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24} : Finset ℕ),
  (A.card = 12 → A.sum id ≥ 110) ∧
  (A.card = 11 → A.sum id ≥ 86) ∧
  (A.card = 10 → A.sum id ≥ 66) ∧
  (A.card = 9 → A.sum id ≥ 51) ∧
  (A.card ≤ 12) := by decide
