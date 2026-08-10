import FormalConjectures.Util.ProblemImports

structure MyPLift (P : Prop) : Type where
  val : PSum P (P → False)
  deriving Nonempty
