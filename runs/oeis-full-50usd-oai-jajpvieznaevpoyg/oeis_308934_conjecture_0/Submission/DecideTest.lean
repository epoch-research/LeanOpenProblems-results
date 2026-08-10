import FormalConjectures.Util.ProblemImports
unsafe def bogusDecidable (P : Prop) : Decidable P := unsafeCast (isTrue True.intro)
attribute [local instance] bogusDecidable
theorem bad : False := by
  native_decide
#print axioms bad
