import FormalConjectures.Util.ProblemImports
#check squarefree_zero
#check not_squarefree_zero
#check Squarefree
example : Squarefree (0:ℤ) := by simp
example : ¬ Squarefree (0:ℤ) := by simp
