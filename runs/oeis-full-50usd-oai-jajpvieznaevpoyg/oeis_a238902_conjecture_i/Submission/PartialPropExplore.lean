import FormalConjectures.Util.ProblemImports

set_option print.axioms true

partial def badDec (P : Prop) [Decidable P] : Decidable P := badDec P

#check Classical.decEq
#check Classical.propComplete
#check Classical.choice
#check Classical.decPred
#check Classical.em

-- try extract
example (P : Prop) [Decidable P] : P := by
  let d := badDec P
  cases d with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (by contradiction)

#print axioms badDec
