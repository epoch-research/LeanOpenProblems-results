import FormalConjectures.Util.ProblemImports
#check Fact
#check inferInstanceAs (Nonempty (Fact True))
#check inferInstanceAs (Nonempty (Fact (Squarefree (0:ℤ))))
example : Fact (Squarefree (0:ℤ)) := Classical.choice (inferInstanceAs (Nonempty (Fact (Squarefree (0:ℤ)))))
