import FormalConjectures.Util.ProblemImports
unsafe def bogusDecidable (P : Prop) : Decidable P := .isTrue (unsafeCast True.intro)
example : False := by
  letI : Decidable False := bogusDecidable False
  native_decide
#print axioms _example
