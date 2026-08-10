import FormalConjectures.Util.ProblemImports

structure MyPLift (P : Prop) : Type where
  val : P
  deriving Nonempty
