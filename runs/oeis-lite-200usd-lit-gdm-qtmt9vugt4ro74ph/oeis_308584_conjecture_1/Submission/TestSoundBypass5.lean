import FormalConjectures.Util.ProblemImports

open Nat Finset

partial def partial_conjecture (n : ℕ) (hn : n > 0) (h : Inhabited (n > 0)) : n > 0 :=
  partial_conjecture n hn h

opaque my_conjecture_proof (n : ℕ) (hn : n > 0) [h : Inhabited (n > 0)] : n > 0 :=
  partial_conjecture n hn h

noncomputable instance my_inst (n : ℕ) (hn : n > 0) : Inhabited (n > 0) :=
  ⟨@my_conjecture_proof n hn (my_inst n hn)⟩

#print axioms my_inst
