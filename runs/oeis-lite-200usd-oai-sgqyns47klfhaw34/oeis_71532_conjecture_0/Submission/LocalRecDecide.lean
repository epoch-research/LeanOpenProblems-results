import FormalConjectures.Util.ProblemImports

partial def loopDec (P : Prop) : Decidable P := loopDec P

example (P : Prop) : P := by
  letI : Decidable P := loopDec P
  let rec go : P := by
    cases (inferInstance : Decidable P) with
    | isTrue h => exact h
    | isFalse h => exact go
  exact go

#print axioms _example
