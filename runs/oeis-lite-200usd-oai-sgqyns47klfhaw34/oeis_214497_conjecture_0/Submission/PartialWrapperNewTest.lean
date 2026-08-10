import FormalConjectures.Util.ProblemImports

partial def nonemptyProp (P : Prop) : Nonempty P := nonemptyProp P
partial def inhabitedProp (P : Prop) : Inhabited P := inhabitedProp P
partial def pliftProp (P : Prop) : PLift P := pliftProp P
partial def subtypeWitness (P : Prop) : {p : Prop // p} := subtypeWitness P

example (P : Prop) : P := Classical.choice (nonemptyProp P)
example (P : Prop) : P := (inhabitedProp P).default
example (P : Prop) : P := (pliftProp P).down
example (P : Prop) : P := (subtypeWitness P).2

#print axioms nonemptyProp
#print axioms inhabitedProp
#print axioms pliftProp
#print axioms subtypeWitness
#print axioms _example
