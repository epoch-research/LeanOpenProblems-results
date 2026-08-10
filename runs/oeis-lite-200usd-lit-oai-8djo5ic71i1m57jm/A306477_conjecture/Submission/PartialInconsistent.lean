import FormalConjectures.Util.ProblemImports
partial def f (n : Nat) : Nat := f n + 1
#check f.eq_def
example : f 0 = f 0 + 1 := by rw [f.eq_def]
theorem bad : False := by
  have h : f 0 = f 0 + 1 := by rw [f.eq_def]
  omega
#print axioms bad
