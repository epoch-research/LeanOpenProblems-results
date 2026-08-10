import FormalConjectures.Util.ProblemImports

def NegP (P : Prop) : Prop := P -> False
inductive Bad : Prop where
| intro : NegP Bad -> Bad
