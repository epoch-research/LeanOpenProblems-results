import FormalConjectures.Util.ProblemImports

inductive MyFlag2 (P : Prop) : Prop where
| mkFalse : MyFlag2 P
| mkTrue : P → MyFlag2 P

partial def extract (P : Prop) (h : MyFlag2 P) : P :=
  match h with
  | MyFlag2.mkTrue hp => hp
  | MyFlag2.mkFalse => extract P h

#print extract
#print axioms extract

example (P : Prop) : P := extract P MyFlag2.mkFalse
#print axioms _example
