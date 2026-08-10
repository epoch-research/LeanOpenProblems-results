import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

def S_14 : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40}

lemma test_14 : ∀ D ⊆ S_14, D.card ≥ 12 → D.sum id > 60 := by decide
