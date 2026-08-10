import FormalConjectures.Util.ProblemImports

partial def my_inst : Nonempty (∀ (P : Prop), Nonempty P) :=
  Nonempty.intro (fun P => Classical.choice my_inst P)

#print axioms my_inst
