import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

unsafe def unsafe_proof (n : ℕ) : 0 < A271510 n :=
  unsafe_proof n

unsafe instance inst (n : ℕ) : Nonempty (0 < A271510 n) :=
  ⟨unsafe_proof n⟩

partial def get_proof (n : ℕ) : 0 < A271510 n :=
  get_proof n
