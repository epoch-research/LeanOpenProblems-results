import FormalConjectures.Util.ProblemImports
axiom P : Prop
structure S where
  p : P := by
    -- try no proof
    contradiction

#check S.mk
example : P := ({} : S).p
