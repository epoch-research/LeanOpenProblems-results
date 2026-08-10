import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

example : a 2 = 9 := by norm_num [a]
example : a 4 = 745 := by norm_num [a]
example : ¬ ((a (2 ^ 2) : ℤ) ≡ a (2 ^ (2 - 1)) [ZMOD (2 ^ (3 * 2 + 3) : ℕ)]) := by
  norm_num [a]

example : a 3 = 82 := by norm_num [a]
example : a 9 = 60085720 := by norm_num [a]
example : ¬ ((a (3 ^ 2) : ℤ) ≡ a (3 ^ (2 - 1)) [ZMOD (3 ^ (3 * 2 + 3) : ℕ)]) := by
  norm_num [a]
