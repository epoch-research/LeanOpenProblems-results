import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

example : ¬ ((a (139 ^ 2) : ℤ) ≡ a (139 ^ (2 - 1)) [ZMOD (139 ^ (3 * 2 + 3) : ℕ)]) := by
  native_decide
