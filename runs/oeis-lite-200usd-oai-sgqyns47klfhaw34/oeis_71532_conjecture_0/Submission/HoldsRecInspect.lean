import FormalConjectures.Util.ProblemImports
abbrev QProp := Quot (fun A B : Prop => A → B)
def qprop (P : Prop) : QProp := Quot.mk _ P
inductive Holds : QProp → Prop where
| intro {P : Prop} : P → Holds (qprop P)
#print Holds.rec
#check Holds.rec
#check Holds.casesOn
#check Holds.noConfusion
