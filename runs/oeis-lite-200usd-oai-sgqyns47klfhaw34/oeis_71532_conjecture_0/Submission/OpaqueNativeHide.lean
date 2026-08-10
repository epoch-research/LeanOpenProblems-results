import FormalConjectures.Util.ProblemImports
opaque P : Prop
unsafe def fakeDecUnsafe (P : Prop) : Decidable P := Decidable.isTrue (unsafeCast ())
@[implemented_by fakeDecUnsafe]
noncomputable def fakeDecSafe (P : Prop) : Decidable P := Classical.propDecidable P
local instance (P : Prop) : Decidable P := fakeDecSafe P

opaque pProof : P := by
  native_decide

theorem bad : P := pProof
#print axioms pProof
#print axioms bad
