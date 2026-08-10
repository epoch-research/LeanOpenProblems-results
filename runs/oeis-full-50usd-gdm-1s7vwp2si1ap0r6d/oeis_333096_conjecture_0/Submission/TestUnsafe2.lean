unsafe def fakeDecidable : Decidable False := unsafeCast ()

@[implementedBy fakeDecidable]
def myDecidable : Decidable False := .isFalse (fun h => h)
