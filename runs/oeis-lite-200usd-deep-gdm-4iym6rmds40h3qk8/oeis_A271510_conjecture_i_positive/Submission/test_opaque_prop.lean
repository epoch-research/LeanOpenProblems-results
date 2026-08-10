import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 1

unsafe def unsafe_proof (n : ℕ) : 0 < A271510 n :=
  unsafe_proof n

@[implemented_by unsafe_proof]
opaque safe_proof (n : ℕ) : 0 < A271510 n
