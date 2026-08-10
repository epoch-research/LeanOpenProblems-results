import FormalConjectures.Util.ProblemImports
open Nat Finset

def f (n:Nat) := if n=0 then 1 else 2
example (n:Nat) : f n > 0 := by
  native_decide +revert
