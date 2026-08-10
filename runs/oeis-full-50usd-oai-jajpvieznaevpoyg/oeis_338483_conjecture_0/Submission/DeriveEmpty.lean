import FormalConjectures.Util.ProblemImports

inductive EmptyP : Prop deriving Inhabited

#check (default : EmptyP)

theorem bad : False := by
  have h : EmptyP := default
  cases h
#print axioms bad
