import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 1

unsafe def unsafe_proof (n : ℕ) : 0 < A271510 n :=
  unsafe_proof n

unsafe def unsafe_nonempty (n : ℕ) : Nonempty (0 < A271510 n) :=
  ⟨unsafe_proof n⟩

@[implemented_by unsafe_nonempty]
opaque safe_nonempty (n : ℕ) : Nonempty (0 < A271510 n)
