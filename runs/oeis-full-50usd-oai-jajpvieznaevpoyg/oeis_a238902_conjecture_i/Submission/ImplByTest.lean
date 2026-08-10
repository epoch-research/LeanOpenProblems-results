import FormalConjectures.Util.ProblemImports

unsafe def fakeFalseDecide : Decidable False := unsafeCast (Decidable.isTrue True.intro)

@[implemented_by fakeFalseDecide]
def safeFalseDecide : Decidable False := Classical.dec False

local instance : Decidable False := safeFalseDecide

example : False := by
  native_decide

#print axioms safeFalseDecide
