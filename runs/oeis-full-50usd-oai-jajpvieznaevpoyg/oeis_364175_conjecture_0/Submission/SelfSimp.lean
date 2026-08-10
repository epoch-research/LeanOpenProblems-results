import FormalConjectures.Util.ProblemImports

@[simp] theorem selfsimp (n : ℕ) : n = n+0 := by
  simp

@[simp] theorem badself (n : ℕ) : n = n+1 := by
  simp
#print axioms badself
