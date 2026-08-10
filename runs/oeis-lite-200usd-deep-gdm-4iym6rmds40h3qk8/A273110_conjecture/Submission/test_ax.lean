import FormalConjectures.Util.ProblemImports

axiom c_nonempty : Nonempty (1 = 2)

theorem test_thm : 1 = 2 := Classical.choice c_nonempty

#print axioms test_thm
