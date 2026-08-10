import FormalConjectures.Util.ProblemImports

instance : TopologicalSpace Empty := ⊥

example : IrreducibleSpace Empty := by
  constructor
  simp [IsPreirreducible]

example : Nonempty Empty := by
  haveI : IrreducibleSpace Empty := by
    constructor
    simp [IsPreirreducible]
  exact IrreducibleSpace.toNonempty

example : False := by
  haveI : IrreducibleSpace Empty := by
    constructor
    simp [IsPreirreducible]
  exact nomatch (Classical.choice (IrreducibleSpace.toNonempty : Nonempty Empty))

#print axioms _example
