import FormalConjectures.Util.ProblemImports

instance topEmpty : Top Empty where
  top := Classical.choice (top_nonempty Empty)

theorem bad : False := nomatch (Classical.choice (top_nonempty Empty))
#print axioms topEmpty
#print axioms bad
