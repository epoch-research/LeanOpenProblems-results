import FormalConjectures.Util.ProblemImports

partial def pliftP (P : Prop) : PLift P := pliftP P

theorem arbitrary1 (P : Prop) : P := (pliftP P).down
#print axioms arbitrary1
