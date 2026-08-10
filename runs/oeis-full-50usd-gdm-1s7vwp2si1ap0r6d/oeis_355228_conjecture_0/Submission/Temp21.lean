import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

def S_120_small : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24}

lemma S_120_small_sum : S_120_small.sum id = 110 := by rfl

lemma S_max1 (x : ℕ) (hx : x ∈ S_120_small) : x ≤ 24 := by decide

lemma S_max2 (x y : ℕ) (hx : x ∈ S_120_small) (hy : y ∈ S_120_small) (hxy : x ≠ y) : x + y ≤ 44 := by decide

lemma S_max3 (x y z : ℕ) (hx : x ∈ S_120_small) (hy : y ∈ S_120_small) (hz : z ∈ S_120_small) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : x + y + z ≤ 59 := by decide
