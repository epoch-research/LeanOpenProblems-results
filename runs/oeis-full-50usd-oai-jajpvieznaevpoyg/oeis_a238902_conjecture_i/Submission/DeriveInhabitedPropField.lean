import FormalConjectures.Util.ProblemImports
structure S (P : Prop) where
  p : P
deriving instance Inhabited for S
#check (default : S False)
theorem bad : False := (default : S False).p
#print axioms bad
