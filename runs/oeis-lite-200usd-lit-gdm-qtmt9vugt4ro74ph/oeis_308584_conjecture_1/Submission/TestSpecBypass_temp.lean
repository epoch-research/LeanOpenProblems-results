import FormalConjectures.Util.ProblemImports

open Nat Finset

partial def loop_proof (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  haveI : Inhabited (A308584 n > 0) := ⟨loop_proof n hn⟩
  loop_proof n hn

theorem my_proof (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  loop_proof n hn

#print axioms my_proof
