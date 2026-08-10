import FormalConjectures.Util.ProblemImports

partial def pl (P : Prop) : PLift P := pl P
partial def ul (P : Prop) : ULift P := ul P
partial def tr (P : Prop) : Trunc P := tr P
#print axioms pl
#print axioms ul
#print axioms tr
example (P : Prop) : P := (pl P).down
example (P : Prop) : P := (ul P).down
example (P : Prop) : P := Trunc.out (tr P)
