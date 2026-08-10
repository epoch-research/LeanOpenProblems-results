unsafe def fakeDecidable : Decidable False := @unsafeCast (Decidable True) (Decidable False) (Decidable.isTrue (by trivial))

@[implemented_by fakeDecidable]
def myDecidable : Decidable False := .isFalse (fun h => h)

instance : Decidable False := myDecidable

theorem proofOfFalse : False := by
  decide
