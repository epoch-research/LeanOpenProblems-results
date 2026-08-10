import FormalConjectures.Util.ProblemImports
inductive Box (P:Prop) where | mk : P -> Box P deriving Nonempty, Inhabited
#check inferInstanceAs (Nonempty (Box False))
#check inferInstanceAs (Inhabited (Box False))
theorem bad : False := by
  let b : Box False := default
  cases b with | mk h => exact h
#print axioms bad
