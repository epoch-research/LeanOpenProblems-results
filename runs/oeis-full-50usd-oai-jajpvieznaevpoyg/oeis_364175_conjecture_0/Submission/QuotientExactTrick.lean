import FormalConjectures.Util.ProblemImports
#check Quotient.exact
#check Quotient.sound

-- Empty carrier makes equivalence proof vacuous, but then there are no representatives.
def emptySetoid (P : Prop) : Setoid PEmpty where
  r _ _ := P
  iseqv := ⟨by intro x; cases x, by intro x; cases x, by intro x; cases x⟩

-- Nonempty carrier cannot make a constant arbitrary relation reflexive without proving it.
-- def badSetoid (P : Prop) : Setoid Unit where
--   r _ _ := P
--   iseqv := ?_
