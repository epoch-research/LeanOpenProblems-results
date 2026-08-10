import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

lemma no_subset_120 : ∀ D ⊆ Nat.divisors 120, D.card ≥ 13 → D.sum id ≠ 120 := by decide
lemma no_subset_144 : ∀ D ⊆ Nat.divisors 144, D.card ≥ 13 → D.sum id ≠ 144 := by decide
lemma no_subset_168 : ∀ D ⊆ Nat.divisors 168, D.card ≥ 13 → D.sum id ≠ 168 := by decide
