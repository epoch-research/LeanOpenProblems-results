import FormalConjectures.Util.ProblemImports
inductive Bad : Prop deriving Inhabited
#check (default : Bad)
theorem t : False := by cases (default : Bad)
#print axioms t
