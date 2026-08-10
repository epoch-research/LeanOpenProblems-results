import FormalConjectures.Util.ProblemImports

open Nat

def choose (n k : ℕ) : ℕ :=
  if n = 1 then 1 else 0

#eval (2 : ℕ).choose 1
