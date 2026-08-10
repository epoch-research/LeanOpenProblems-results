import FormalConjectures.Util.ProblemImports

unsafe def fakeFalseDecide : Decidable False := unsafeCast (Decidable.isTrue True.intro)
@[implemented_by fakeFalseDecide]
def safeFalseDecide : Decidable False := Classical.dec False
local instance : Decidable False := safeFalseDecide

opaque badOpaque : False := by
  native_decide

theorem bad : False := badOpaque
#print axioms badOpaque
#print axioms bad
