import FormalConjectures.Util.ProblemImports

#check proof_irrel_heq
#print proof_irrel_heq
#print axioms proof_irrel_heq
#check proof_irrel
#print proof_irrel
#check Eq.ndrec
#check Eq.rec
#check cast
#check eq_mpr
#check propext
#check Classical.choice
#check Classical.decEq
#check Classical.choice (Classical.instNonemptyDecidable False)
#reduce Classical.choice (Classical.instNonemptyDecidable False)

example (P : Prop) : P := by
  classical
  let d : Decidable P := Classical.choice (Classical.instNonemptyDecidable P)
  cases d with
  | isTrue h => exact h
  | isFalse h => exact?
