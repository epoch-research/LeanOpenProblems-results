import FormalConjectures.Util.ProblemImports

theorem bad : False := nomatch (Part.unwrap (Part.none : Part Empty))
#print axioms bad
