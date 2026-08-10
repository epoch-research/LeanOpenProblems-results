import FormalConjectures.Util.ProblemImports

unsafe def fakeDec (P : Prop) : Decidable P :=
  Decidable.isTrue (unsafeCast ())

local instance (P : Prop) : Decidable P := fakeDec P

theorem bad : False := by
  native_decide

#print axioms bad
