import FormalConjectures.Util.ProblemImports

example : (Or.inl True.intro : True ∨ True) = Or.inr True.intro := by
  apply Subsingleton.elim

example : (Or.inl True.intro : True ∨ True) = Or.inr True.intro → False := by
  intro h
  cases h
