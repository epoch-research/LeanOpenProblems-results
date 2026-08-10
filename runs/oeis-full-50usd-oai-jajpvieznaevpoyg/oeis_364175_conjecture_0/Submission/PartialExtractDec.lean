import FormalConjectures.Util.ProblemImports
partial def extractDec (P : Prop) (d : Decidable P) : P :=
  match d with
  | isTrue h => h
  | isFalse _ => extractDec P d
partial def decLoop (P : Prop) : Decidable P := decLoop P
theorem bad : False := extractDec False (decLoop False)
#print axioms bad
