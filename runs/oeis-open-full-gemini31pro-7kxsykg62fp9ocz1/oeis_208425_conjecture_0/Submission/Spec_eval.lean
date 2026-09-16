import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

def a (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    (n.choose k) * ((n - k).choose k) * ((n + k).choose k)

#eval a 1
#eval a 2
#eval a 3
#eval a 4
#eval a 5
#eval a 6
