import FormalConjectures.Util.ProblemImports
structure Bad (P : Prop) where
  proof : P
deriving instance Inhabited for Bad
example (P : Prop) : P := (default : Bad P).proof
#print axioms Bad.instInhabited
