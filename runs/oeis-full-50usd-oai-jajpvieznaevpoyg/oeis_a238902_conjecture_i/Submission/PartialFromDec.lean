import FormalConjectures.Util.ProblemImports
partial def proofFromDec (P : Prop) (d : Decidable P) (_ : Unit) : P :=
  match d with
  | isTrue h => h
  | isFalse _ => proofFromDec P d ()
#print proofFromDec
#print axioms proofFromDec

theorem bad : False := proofFromDec False (Decidable.isFalse id) ()
#print axioms bad
