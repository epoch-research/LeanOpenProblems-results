import FormalConjectures.Util.ProblemImports

partial def dneLoop (P : Prop) : ¬¬P → P := fun hnn => dneLoop P hnn
partial def contraLoop (P Q : Prop) : (P → Q) → (¬P → Q) → Q := fun hp hn => contraLoop P Q hp hn
partial def peirceLoop (P Q : Prop) : ((P → Q) → P) → P := fun h => peirceLoop P Q h
partial def emLoop (P : Prop) : P ∨ ¬P := emLoop P

#print dneLoop
#print contraLoop
#print peirceLoop
#print emLoop
#print axioms dneLoop
#print axioms contraLoop
#print axioms peirceLoop
#print axioms emLoop

example (P : Prop) : P := dneLoop P (fun hp => hp.elim)
#print axioms _example
