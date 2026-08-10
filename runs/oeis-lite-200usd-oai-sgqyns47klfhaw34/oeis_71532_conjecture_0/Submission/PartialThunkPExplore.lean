import FormalConjectures.Util.ProblemImports

def ThunkP (P : Prop) : Type := Unit → P
partial def thunkP (P : Prop) : ThunkP P := thunkP P

theorem arbitrary1 (P : Prop) : P := (thunkP P) ()
#print axioms arbitrary1
