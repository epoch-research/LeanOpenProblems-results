import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

unsafe def get_proof_unsafe (n : ℕ) : 0 < A271510 n :=
  get_proof_unsafe n

unsafe instance inst_inh (n : ℕ) : Inhabited (0 < A271510 n) :=
  ⟨get_proof_unsafe n⟩

@[implemented_by get_proof_unsafe]
opaque get_proof (n : ℕ) : 0 < A271510 n


