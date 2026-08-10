import FormalConjectures.Util.ProblemImports
#check (inferInstance : Nonempty (Subsingleton ℕ))
#check (Classical.choice (inferInstance : Nonempty (Subsingleton ℕ)) : Subsingleton ℕ)
example : (0:ℕ)=1 := by
  letI : Subsingleton ℕ := Classical.choice (inferInstance : Nonempty (Subsingleton ℕ))
  exact Subsingleton.elim _ _
#print axioms this
