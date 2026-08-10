import FormalConjectures.Util.ProblemImports
structure Box (P : Prop) where
  val : P
  deriving Nonempty

theorem arb (P : Prop) : P := (Classical.choice (inferInstance : Nonempty (Box P))).val
#print axioms arb
