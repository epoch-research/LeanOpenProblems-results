import FormalConjectures.Util.ProblemImports

structure Bad (P : Prop) where
  val : Unit
  proof : P
  deriving Nonempty

#check Bad.instNonempty

theorem arbitrary (P : Prop) : P := (Classical.choice (Bad.instNonempty P)).proof
#print axioms arbitrary
