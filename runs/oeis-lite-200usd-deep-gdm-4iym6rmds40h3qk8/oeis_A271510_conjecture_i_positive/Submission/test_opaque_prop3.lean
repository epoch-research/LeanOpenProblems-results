import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 1

unsafe def unsafe_proof (n : ℕ) : 0 < A271510 n :=
  unsafe_proof n

unsafe def inst_inh_unsafe (n : ℕ) : Inhabited (0 < A271510 n) :=
  ⟨unsafe_proof n⟩

@[implemented_by inst_inh_unsafe]
opaque inst_inh (n : ℕ) : Inhabited (0 < A271510 n)

attribute [instance] inst_inh

opaque safe_proof (n : ℕ) : 0 < A271510 n
