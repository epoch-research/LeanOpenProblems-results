import FormalConjectures.Util.ProblemImports

partial def infUnit (_ : Unit) : Infinite PUnit := infUnit ()
noncomputable instance : Infinite PUnit := infUnit ()
example : False := by
  exact Infinite.not_finite (α := PUnit) (Set.finite_univ.to_subtype)
#print axioms infUnit
#print axioms PartialFalseClassProp._example_1
