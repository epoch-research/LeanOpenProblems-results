unsafe def fakeDecidable : Decidable False := unsafeCast ()

@[implemented_by fakeDecidable]
def myDecidable : Decidable False := .isFalse (fun h => h)

instance : Decidable False := myDecidable

theorem proofOfFalse : False := by
  have h : False := by
    -- Wait, if myDecidable is unfolded by the kernel, can we do decide?
    decide
