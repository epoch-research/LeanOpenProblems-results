import FormalConjectures.Util.ProblemImports
opaque opqFalse : False
#print axioms opqFalse
noncomputable def viaChoice (P : Prop) [h : Nonempty P] : P := Classical.choice h
#print axioms viaChoice
