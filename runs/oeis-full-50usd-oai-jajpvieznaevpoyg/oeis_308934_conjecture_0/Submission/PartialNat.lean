import FormalConjectures.Util.ProblemImports
partial def f (n : Nat) : Nat := if n=0 then 0 else f (n-1)
theorem t : f 3 = 0 := by native_decide
#print axioms t
#print f
