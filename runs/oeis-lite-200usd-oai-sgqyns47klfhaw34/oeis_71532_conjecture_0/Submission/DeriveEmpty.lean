import FormalConjectures.Util.ProblemImports

inductive Empty2 where

deriving instance Inhabited for Empty2

example : False := by
  have e : Empty2 := default
  cases e
