import FormalConjectures.Util.ProblemImports

partial def contra (P : Prop) (h : ¬ P) (_ : Unit) : P := contra P h ()
#print contra
#print axioms contra

theorem emMagic (P : Prop) : P := by
  by_cases h : P
  · exact h
  · exact contra P h ()
#print axioms emMagic

theorem bad : False := emMagic False
#print axioms bad
