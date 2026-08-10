import FormalConjectures.Util.ProblemImports

partial instance topSelf (α : Type u) : Top α where
  top := (⊤ : α)

theorem bad : False := Classical.choice (top_nonempty False)
#print axioms topSelf
#print axioms bad
