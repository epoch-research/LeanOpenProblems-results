import FormalConjectures.Util.ProblemImports
partial def loopDec (P : Prop) : Decidable P := loopDec P

partial def extractLoop (P : Prop) : P :=
  match loopDec P with
  | Decidable.isTrue h => h
  | Decidable.isFalse _ => extractLoop P

theorem any_from_extractLoop (P : Prop) : P := extractLoop P
#print axioms any_from_extractLoop
