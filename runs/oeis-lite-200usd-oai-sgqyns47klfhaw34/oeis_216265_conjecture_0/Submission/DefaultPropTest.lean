import FormalConjectures.Util.ProblemImports
#check (default : Prop)
example : (default : Prop) := by trivial
example : (default : Prop) = True := rfl
-- Cannot cast to arbitrary P without equality.
