import FormalConjectures.Util.ProblemImports

open Nat

def Nat.choose (n k : ℕ) : ℕ :=
  if n = 1 then 1 else 0
