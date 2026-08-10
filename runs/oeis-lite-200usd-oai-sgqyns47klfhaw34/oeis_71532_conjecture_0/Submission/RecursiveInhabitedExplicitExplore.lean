import FormalConjectures.Util.ProblemImports

instance instInhabitedPropOfDec (P : Prop) [Decidable P] : Inhabited P where
  default := by
    cases (inferInstance : Decidable P) with
    | isTrue h => exact h
    | isFalse hn => exact False.elim (hn (instInhabitedPropOfDec P).default)

theorem arbitrary (P : Prop) : P := by
  classical
  exact (default : P)

#print axioms arbitrary
