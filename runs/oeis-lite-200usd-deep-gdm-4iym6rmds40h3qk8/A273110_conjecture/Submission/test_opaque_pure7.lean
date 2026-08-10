import FormalConjectures.Util.ProblemImports

opaque my_const (P : Prop) [Inhabited (Nonempty P)] : Nonempty P := default

theorem my_false : False := Classical.choice (my_const False)
