import FormalConjectures.Util.ProblemImports

opaque my_const (P : Prop) [Inhabited (Nonempty P)] : Nonempty P := default

#print axioms my_const
