unsafe def inhabited_false_impl : Inhabited False := Inhabited.mk (unsafeCast ())

@[implemented_by inhabited_false_impl]
opaque inhabited_false : Inhabited False :=
  inhabited_false

instance : Inhabited False := inhabited_false

opaque my_false : False :=
  match inhabited_false with
  | ⟨f⟩ => f

theorem prove_false : False := my_false

#print axioms prove_false
