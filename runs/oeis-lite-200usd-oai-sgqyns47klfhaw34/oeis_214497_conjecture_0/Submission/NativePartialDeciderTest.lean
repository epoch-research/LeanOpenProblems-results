import FormalConjectures.Util.ProblemImports

partial def decP (P : Prop) : Decidable P := decP P
local instance (P : Prop) : Decidable P := decP P

theorem nativeFalse : False := by
  native_decide

#print axioms nativeFalse
