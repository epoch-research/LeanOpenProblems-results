import FormalConjectures.Util.ProblemImports

partial def badPart (_ : Unit) : Part Empty := ⟨True, fun _ => (badPart ()).get (by trivial)⟩

#reduce (badPart ()).Dom
#print badPart

theorem badEmpty : Empty := (badPart ()).get (by trivial)
theorem bad : False := nomatch badEmpty
#print axioms badPart
#print axioms badEmpty
#print axioms bad
