import FormalConjectures.Util.ProblemImports
#check False.elim
#check Classical.choice
example : ¬ False := by intro h; exact h
-- exact? for False should fail
example : False := by
  exact?
