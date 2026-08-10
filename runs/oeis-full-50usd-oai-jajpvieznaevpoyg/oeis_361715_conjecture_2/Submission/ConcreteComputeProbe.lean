import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

example : a 5 = 6876 := by
  native_decide

example : ¬ ((a (5 ^ 2) : ℤ) ≡ a (5 ^ (2 - 1)) [ZMOD (5 ^ (3 * 2 + 3) : ℕ)]) := by
  norm_num [a]
