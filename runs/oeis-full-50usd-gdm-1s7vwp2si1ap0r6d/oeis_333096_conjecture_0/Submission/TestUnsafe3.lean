unsafe def fakeDecidable : Decidable False := unsafeCast ()

@[implemented_by fakeDecidable]
def myDecidable : Decidable False := .isFalse (fun h => h)
