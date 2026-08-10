import FormalConjectures.Util.ProblemImports

structure MyStruct (P : Prop) where
  val : Inhabited (Nonempty P)
deriving Nonempty
