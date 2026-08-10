import FormalConjectures.Util.ProblemImports

def my_prop : Prop := answer(sorry)

theorem my_thm : my_prop := by
  unfold my_prop
  trivial

#print axioms my_thm
