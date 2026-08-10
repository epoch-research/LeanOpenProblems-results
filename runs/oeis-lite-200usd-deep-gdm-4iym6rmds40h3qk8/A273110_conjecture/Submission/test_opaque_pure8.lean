import FormalConjectures.Util.ProblemImports

opaque my_const (P : Prop) [Inhabited (Nonempty P)] : Nonempty P := default

instance my_inst (P : Prop) : Inhabited (Nonempty P) where
  default := @my_const P (my_inst P)

theorem my_false : False := Classical.choice (my_const False)

#print axioms my_false
