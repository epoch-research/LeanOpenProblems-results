import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

#eval a 5
#eval (a 25 - a 5) % (5^9)
#eval a 7
#eval (a 49 - a 7) % (7^9)
