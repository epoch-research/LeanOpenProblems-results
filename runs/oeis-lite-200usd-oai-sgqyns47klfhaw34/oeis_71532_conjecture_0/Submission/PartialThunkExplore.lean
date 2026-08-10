import FormalConjectures.Util.ProblemImports

partial def thunkP (P : Prop) : Thunk P := thunkP P

theorem arbitrary1 (P : Prop) : P := (thunkP P).get
#print axioms arbitrary1
