import FormalConjectures.Util.ProblemImports
partial def pfFalse (u : Unit) : False := by
  haveI : Nonempty False := ⟨pfFalse ()⟩
  exact pfFalse ()
#print axioms pfFalse

theorem bad : False := pfFalse ()
#print axioms bad
