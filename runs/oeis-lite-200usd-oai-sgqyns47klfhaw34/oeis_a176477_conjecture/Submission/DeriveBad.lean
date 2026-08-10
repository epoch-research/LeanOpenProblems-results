import FormalConjectures.Util.ProblemImports
structure Bad : Prop where
  pf : False
deriving instance Inhabited for Bad
example : False := (default : Bad).pf
