import FormalConjectures.Util.ProblemImports
inductive Wrap (P : Prop) : Prop where | mk : P → Wrap P deriving Inhabited
#check (default : Wrap False)
example : False := by cases (default : Wrap False) with | mk h => exact h
#print axioms this
