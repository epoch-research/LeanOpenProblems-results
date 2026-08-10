import FormalConjectures.Util.ProblemImports

open Nat Finset

opaque my_conjecture_proof (n : ℕ) (hn : n > 0) : n > 0

noncomputable instance my_inst (n : ℕ) (hn : n > 0) : Inhabited (n > 0) :=
  ⟨my_conjecture_proof n hn⟩

#print axioms my_inst
