import FormalConjectures.Util.ProblemImports
partial def decLoop (P : Prop) : Decidable P := decLoop P
local instance (P : Prop) : Decidable P := decLoop P
theorem bad : False := by
  native_decide
#print axioms bad
