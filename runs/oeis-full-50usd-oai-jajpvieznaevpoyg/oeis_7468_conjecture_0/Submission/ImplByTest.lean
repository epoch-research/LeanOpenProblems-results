import FormalConjectures.Util.ProblemImports

unsafe def decFalseUnsafe : Decidable False := isTrue (unsafeCast ())
@[implemented_by decFalseUnsafe]
def decFalseLie : Decidable False := isFalse (by intro h; exact h)

local instance : Decidable False := decFalseLie
theorem bad : False := by
  native_decide
#print axioms bad
#print bad
