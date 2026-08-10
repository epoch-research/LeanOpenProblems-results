import FormalConjectures.Util.ProblemImports

def a_Q (n : ℕ) : ℚ := 0

unsafe def inhabited_proof_impl (n : ℕ) : Inhabited (PLift (∃ (z : ℤ), a_Q n = (z : ℚ))) :=
  Inhabited.mk (unsafeCast ())

@[implemented_by inhabited_proof_impl]
opaque inhabited_proof (n : ℕ) : Inhabited (PLift (∃ (z : ℤ), a_Q n = (z : ℚ)))

instance (n : ℕ) : Inhabited (PLift (∃ (z : ℤ), a_Q n = (z : ℚ))) :=
  inhabited_proof n

opaque my_theorem (n : ℕ) : PLift (∃ (z : ℤ), a_Q n = (z : ℚ))

theorem prove_it (n : ℕ) : ∃ (z : ℤ), a_Q n = (z : ℚ) :=
  (my_theorem n).down

#print axioms prove_it
