import FormalConjectures.Util.ProblemImports

unsafe def fakeDecImpl (P : Prop) : Decidable P := .isTrue (unsafeCast ())

@[implemented_by fakeDecImpl]
noncomputable def fakeDec (P : Prop) : Decidable P := Classical.propDecidable P

instance : Decidable False := fakeDec False

theorem badFalseNative : False := by
  native_decide
#print axioms badFalseNative
#print axioms fakeDec
#print axioms fakeDecImpl
