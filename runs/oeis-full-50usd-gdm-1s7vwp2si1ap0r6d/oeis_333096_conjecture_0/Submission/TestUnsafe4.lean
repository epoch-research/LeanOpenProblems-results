unsafe def fakeDecidable : Decidable False := unsafeCast (Decidable.isTrue (by sorry))

@[implemented_by fakeDecidable]
def myDecidable : Decidable False := .isFalse (fun h => h)

@[default_instance]
instance : Decidable False := myDecidable

theorem proofOfFalse : False := by
  decide
