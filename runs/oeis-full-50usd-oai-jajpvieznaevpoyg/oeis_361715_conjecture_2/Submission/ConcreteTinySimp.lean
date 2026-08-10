import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

example : Nat.choose 4 2 = 6 := by simp [Nat.choose]
example : Nat.choose 6 3 = 20 := by simp [Nat.choose]
example : a 2 = 9 := by simp [a, Nat.choose, Nat.multichoose_eq]
example : a 3 = 82 := by simp [a, Nat.choose, Nat.multichoose_eq]
example : a 4 = 745 := by simp [a, Nat.choose, Nat.multichoose_eq]
