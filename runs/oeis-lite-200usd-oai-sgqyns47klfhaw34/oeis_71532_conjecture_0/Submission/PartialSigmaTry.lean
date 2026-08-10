import FormalConjectures.Util.ProblemImports

partial def badSigma (P : Prop) : {Q : Prop // Q} := ⟨P, (badSigma P).2⟩

#check badSigma
#check (badSigma False).2
example : False := (badSigma False).2
#print axioms badSigma
#print axioms _example
