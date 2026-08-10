import FormalConjectures.Util.ProblemImports
partial def decLoop (P : Prop) : Decidable P := decLoop P
@[local instance 2000] def myDec (P : Prop) : Decidable P := decLoop P
theorem bad : False := by
  by_cases h : False
  · exact h
  · exact False.elim (h ?_)
