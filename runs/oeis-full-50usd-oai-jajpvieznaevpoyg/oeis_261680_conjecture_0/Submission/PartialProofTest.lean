import FormalConjectures.Util.ProblemImports
open Nat List Finset

def a (n : Nat) := n+1
partial def pf (n : Nat) : a n > 0 := pf n
#print axioms pf
