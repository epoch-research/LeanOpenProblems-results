import FormalConjectures.Util.ProblemImports

mutual
  partial def my_inst (P : Prop) [h : Inhabited (Nonempty P)] : Nonempty P :=
    my_inst P

  @[instance]
  partial def my_inhabited_inst (P : Prop) : Inhabited (Nonempty P) :=
    ⟨my_inst P⟩
end

#print axioms my_inst
