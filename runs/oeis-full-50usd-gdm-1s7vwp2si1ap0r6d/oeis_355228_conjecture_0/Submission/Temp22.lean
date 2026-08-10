import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

def S_120_small : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24}

lemma S_120_small_sum : S_120_small.sum id = 110 := by rfl

lemma S_max1 : ∀ x ∈ S_120_small, x ≤ 24 := by decide

lemma S_max2 : ∀ x ∈ S_120_small, ∀ y ∈ S_120_small, x ≠ y → x + y ≤ 44 := by decide

lemma S_max3 : ∀ x ∈ S_120_small, ∀ y ∈ S_120_small, ∀ z ∈ S_120_small, x ≠ y → y ≠ z → x ≠ z → x + y + z ≤ 59 := by decide
