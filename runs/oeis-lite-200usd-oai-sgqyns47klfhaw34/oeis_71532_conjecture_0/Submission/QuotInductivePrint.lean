import FormalConjectures.Util.ProblemImports

def Q : Sort 1 := Quot (fun (_ _ : Prop) => True)
def q (P : Prop) : Q := Quot.mk _ P
inductive I : Q → Prop where
| intro {P : Prop} (p : P) : I (q P)
#print I
#print I.rec
#print I.casesOn
#print I.noConfusion
#check I.rec
#check @I.rec
#check @I.casesOn
