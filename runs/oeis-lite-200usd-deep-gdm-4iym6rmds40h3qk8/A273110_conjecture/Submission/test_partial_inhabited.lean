import FormalConjectures.Util.ProblemImports

partial def my_partial_h (P : Prop) (u : Unit) : Inhabited (Nonempty P) :=
  my_partial_h P ()

#print axioms my_partial_h
