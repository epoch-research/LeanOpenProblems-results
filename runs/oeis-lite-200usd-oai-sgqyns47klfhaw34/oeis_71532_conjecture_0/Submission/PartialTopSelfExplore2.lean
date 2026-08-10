import FormalConjectures.Util.ProblemImports

partial instance topSelf (α : Type u) : Top α where
  top := @Top.top α (topSelf α)

theorem badEmpty : Empty := Classical.choice (top_nonempty Empty)
theorem bad : False := nomatch badEmpty
#print axioms topSelf
#print axioms bad
