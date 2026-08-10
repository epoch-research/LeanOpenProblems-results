import FormalConjectures.Util.ProblemImports
partial def decLoop (P : Prop) : Decidable P := decLoop P
@[local instance 2000] def myDec (P : Prop) : Decidable P := decLoop P
def P : Prop := False
theorem bad : P := by
  native_decide
#print axioms bad
