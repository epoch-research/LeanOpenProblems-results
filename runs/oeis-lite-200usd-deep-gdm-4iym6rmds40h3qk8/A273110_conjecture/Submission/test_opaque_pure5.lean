import FormalConjectures.Util.ProblemImports

opaque my_const (P : Prop) [Inhabited (Nonempty P)] : Nonempty P
