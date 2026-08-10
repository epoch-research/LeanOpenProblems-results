import FormalConjectures.Util.ProblemImports

abbrev QBool := Quot (fun _ _ : Bool => True)
def q (b : Bool) : QBool := Quot.mk _ b

inductive I : QBool → Type where
| c0 : I (q false)
| c1 : I (q true)

#print I.noConfusion
#check I.noConfusion
#check I.noConfusionType
