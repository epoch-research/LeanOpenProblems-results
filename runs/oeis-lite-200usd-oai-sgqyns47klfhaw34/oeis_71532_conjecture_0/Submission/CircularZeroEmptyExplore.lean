import FormalConjectures.Util.ProblemImports

noncomputable instance zeroEmpty : Zero Empty where
  zero := @Classical.choice Empty (@Zero.instNonempty Empty zeroEmpty)

theorem bad : False := nomatch (@Classical.choice Empty (@Zero.instNonempty Empty zeroEmpty))
#print axioms zeroEmpty
#print axioms bad
