import FormalConjectures.Util.ProblemImports
inductive Loopy : Prop where
| intro : (Loopy -> False) -> Loopy

theorem loopy : Loopy := by
  by_cases h : Loopy
  · exact h
  · exact Loopy.intro h

theorem bad : False := by
  cases loopy with
  | intro f => exact f loopy
#print axioms bad
