import FormalConjectures.Util.ProblemImports
inductive Bad : Prop deriving Inhabited
#check (default : Bad)
#print axioms Bad.instInhabited
example : False := by cases (default : Bad)
#print axioms _example
