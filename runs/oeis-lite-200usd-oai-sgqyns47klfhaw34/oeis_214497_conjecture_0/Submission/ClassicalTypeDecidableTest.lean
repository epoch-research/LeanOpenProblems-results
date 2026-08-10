import FormalConjectures.Util.ProblemImports

#check Classical.typeDecidable
#check Classical.instNonemptyDecidable
#check Classical.propDecidable
#check Classical.propComplete

example (α : Sort u) : Decidable (Nonempty α) := Classical.typeDecidable α

example (P : Prop) : Decidable P := Classical.propDecidable P

example (P : Prop) : P := by
  have hdec : Decidable P := Classical.propDecidable P
  cases hdec with
  | isTrue h => exact h
  | isFalse h =>
    -- no contradiction
    exact?
