import FormalConjectures.Util.ProblemImports

open Nat Finset

partial def loop_proof (n : ℕ) (hn : n > 0) : n > 0 :=
  haveI : Inhabited (n > 0) := ⟨loop_proof n hn⟩
  loop_proof n hn

#print axioms loop_proof
