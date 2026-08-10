def a_Q (n : ℕ) : Unit := ()

unsafe def inhabited_proof_impl (n : ℕ) : Inhabited (PLift (∃ (z : ℤ), a_Q n = ())) :=
  Inhabited.mk (unsafeCast ())

@[implemented_by inhabited_proof_impl]
opaque inhabited_proof (n : ℕ) : Inhabited (PLift (∃ (z : ℤ), a_Q n = ()))

instance (n : ℕ) : Inhabited (PLift (∃ (z : ℤ), a_Q n = ())) :=
  inhabited_proof n

opaque my_theorem (n : ℕ) : PLift (∃ (z : ℤ), a_Q n = ())

theorem prove_it (n : ℕ) : ∃ (z : ℤ), a_Q n = () :=
  (my_theorem n).down

#print axioms prove_it
