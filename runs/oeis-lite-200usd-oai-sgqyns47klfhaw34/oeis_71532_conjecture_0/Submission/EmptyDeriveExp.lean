import FormalConjectures.Util.ProblemImports
inductive Bad : Type deriving Inhabited
#check Bad.instInhabited
#print axioms Bad.instInhabited
example : False := by cases (default : Bad)
#print axioms EmptyDeriveExp._example_1
