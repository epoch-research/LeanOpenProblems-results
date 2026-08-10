import FormalConjectures.Util.ProblemImports
partial def f (n : Nat) : Nat := if n = 0 then 0 else f (n-1)
#print f
#print axioms f
#check f.eq_1
#print f.eq_1
example : f 0 = 0 := by rw [f.eq_1]; simp
#print axioms _example
