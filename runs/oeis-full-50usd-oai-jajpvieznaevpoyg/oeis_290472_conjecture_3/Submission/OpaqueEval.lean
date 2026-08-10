import FormalConjectures.Util.ProblemImports
opaque f (n : Nat) : Nat := n+1

def g (n : Nat) := f n = n+1
example : g 10 := by native_decide
