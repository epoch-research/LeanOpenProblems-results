import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

example : ¬ ((a (3 ^ 2) : ℤ) ≡ a (3 ^ (2 - 1)) [ZMOD (3 ^ (3 * 2 + 3) : ℕ)]) := by
  native_decide
