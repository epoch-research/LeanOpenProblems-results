import FormalConjectures.Util.ProblemImports

noncomputable instance topEmpty : Top Empty where
  top := @Classical.choice Empty ( Empty topEmpty)

theorem bad : False := nomatch (@Classical.choice Empty (top_nonempty Empty))
#print axioms topEmpty
#print axioms bad
