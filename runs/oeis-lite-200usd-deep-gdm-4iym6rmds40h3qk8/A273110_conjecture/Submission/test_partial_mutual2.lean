import FormalConjectures.Util.ProblemImports

mutual
  partial def my_partial_nonempty (P : Prop) : Nonempty P :=
    my_partial_nonempty P

  @[instance]
  partial def my_inst (P : Prop) : Nonempty (Nonempty P) :=
    Nonempty.intro (my_partial_nonempty P)
end

#print axioms my_partial_nonempty
