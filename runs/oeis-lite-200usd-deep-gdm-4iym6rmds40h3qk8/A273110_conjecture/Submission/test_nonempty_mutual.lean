import FormalConjectures.Util.ProblemImports

mutual
  @[instance]
  partial def my_inst_inst (u : Unit) : Nonempty (Nonempty (∀ (P : Prop), Nonempty P)) :=
    Nonempty.intro (my_inst ())

  partial def my_inst (u : Unit) : Nonempty (∀ (P : Prop), Nonempty P) :=
    Nonempty.intro (fun P => Classical.choice (my_inst ()) P)
end

#print axioms my_inst
