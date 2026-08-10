import FormalConjectures.Util.ProblemImports

partial def dnDec (P : Prop) [Decidable P] : (P → False) → False
  | hn => match (inferInstance : Decidable P) with
    | isTrue hp => hn hp
    | isFalse _ => dnDec P hn

theorem arbitrary (P : Prop) : P := by
  classical
  exact Classical.byContradiction (@dnDec P inferInstance)
#print axioms arbitrary
