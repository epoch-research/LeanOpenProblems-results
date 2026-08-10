import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

example : a 2 = 9 := by
  rw [a]
  simp [Nat.multichoose_eq]
  norm_num [Nat.choose]

example : a 2 = 9 := by
  decide +kernel
