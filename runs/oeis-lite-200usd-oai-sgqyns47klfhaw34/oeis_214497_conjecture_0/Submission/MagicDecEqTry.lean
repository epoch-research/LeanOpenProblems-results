import FormalConjectures.Util.ProblemImports

partial def magicDecidable (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    have h : @decide P (magicDecidable P) = true := by
      unfold decide
      -- try unfold magicDecidable
      simp [magicDecidable]
    exact @of_decide_eq_true P (magicDecidable P) h)

#check magicDecidable
#print axioms magicDecidable
