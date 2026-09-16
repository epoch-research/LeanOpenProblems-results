import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma sub_ge_2 (m p : ℕ) (hp2 : p ≥ 2) (hp_le : p ≤ m / 2) : 2 ≤ m - p := by
  omega

