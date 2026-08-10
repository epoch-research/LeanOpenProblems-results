import FormalConjectures.Util.ProblemImports
example (P : Prop) : Subsingleton P := inferInstance
#check (inferInstance : Inhabited True)
#check (inferInstance : Nonempty True)
-- #check (inferInstance : Inhabited False)
-- #check (inferInstance : ∀ P : Prop, Inhabited P)
example (P : Prop) [Inhabited P] : P := default
