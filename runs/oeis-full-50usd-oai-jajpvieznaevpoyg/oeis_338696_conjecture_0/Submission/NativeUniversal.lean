import FormalConjectures.Util.ProblemImports

noncomputable def decFalse : Decidable False := Classical.dec _
unsafe def decFalseImpl : Decidable False := isTrue (unsafeCast ())
attribute [implemented_by decFalseImpl] decFalse
local instance : Decidable False := decFalse

theorem falseNative : False := by
  native_decide
#print axioms falseNative
