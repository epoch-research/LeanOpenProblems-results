def fakeDecidable : Decidable False := unsafeCast ()

-- Wait, unsafeCast needs to be in an unsafe definition, or can it be used in a normal definition?
-- Actually, let us check if we can define fakeDecidable.
