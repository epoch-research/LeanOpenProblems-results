import FormalConjectures.Util.ProblemImports
unsafe def fakeFalseDecide : Decidable False := unsafeCast (Decidable.isTrue True.intro)
@[implemented_by fakeFalseDecide]
def safeFalseDecide : Decidable False := Classical.dec False
local instance : Decidable False := safeFalseDecide

theorem bad : False := by
  exact if h : False then h else False.elim (h (by native_decide))

#print axioms bad
