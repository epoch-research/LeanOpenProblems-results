import FormalConjectures.Util.ProblemImports

open Nat

def Nat.choose (n k : ℕ) : ℕ :=
  if n = 1 then _root_.Nat.choose n k
  else if k = 1 then 1 else 0
