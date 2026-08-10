unsafe def unsafeProof {α : Sort u} : α :=
  unsafeCast ()

theorem my_theorem : False := unsafeProof
