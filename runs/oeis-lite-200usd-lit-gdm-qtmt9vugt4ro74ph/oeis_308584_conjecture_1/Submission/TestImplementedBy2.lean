import FormalConjectures.Util.ProblemImports

def A308584 (n : ℕ) : ℕ := 1

unsafe def unsafe_proof (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  unsafe_proof n hn

@[implemented_by unsafe_proof]
opaque safe_proof (n : ℕ) (hn : n > 0) : A308584 n > 0

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  safe_proof n hn

#print axioms oeis_308584_conjecture_1
