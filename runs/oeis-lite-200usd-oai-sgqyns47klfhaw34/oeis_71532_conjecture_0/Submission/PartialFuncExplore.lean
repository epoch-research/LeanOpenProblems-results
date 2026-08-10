import FormalConjectures.Util.ProblemImports

-- Which proof-ish function types can partial accept?
partial def f1 (P : Prop) : Empty → P := f1 P
partial def f2 (P : Prop) : P → False := f2 P
partial def f3 (P : Prop) : (P → False) → P := f3 P
partial def f4 (P : Prop) : ((P → False) → False) → P := f4 P
partial def f5 (P Q : Prop) : (P → Q) := f5 P Q
partial def f6 (P : Prop) : Unit → P := f6 P
partial def f7 (P : Prop) : Nat → P := f7 P

#print axioms f1
#print axioms f2
#print axioms f3
#print axioms f4
#print axioms f5
#print axioms f6
#print axioms f7
