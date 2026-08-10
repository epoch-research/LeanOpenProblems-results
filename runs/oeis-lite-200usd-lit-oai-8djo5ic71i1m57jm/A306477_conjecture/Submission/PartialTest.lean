import FormalConjectures.Util.ProblemImports
partial def f (n : Nat) : Nat := if n=0 then 0 else f (n-1)+1
theorem t : f 10 = 10 := by native_decide
#print axioms t
#print f
