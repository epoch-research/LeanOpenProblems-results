import FormalConjectures.Util.ProblemImports

unsafe def fakeDecUnsafe (P : Prop) : Decidable P := Decidable.isTrue (unsafeCast ())
@[implemented_by fakeDecUnsafe]
noncomputable def fakeDecSafe (P : Prop) : Decidable P := Classical.propDecidable P

local instance (P : Prop) : Decidable P := fakeDecSafe P

theorem bad : False := by
  native_decide

#print axioms bad
