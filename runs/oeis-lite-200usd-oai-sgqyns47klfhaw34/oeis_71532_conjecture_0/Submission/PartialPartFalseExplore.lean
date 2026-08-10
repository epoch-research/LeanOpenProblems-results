import FormalConjectures.Util.ProblemImports

partial def badPart (_ : Unit) : Part False := ⟨True, fun _ => (badPart ()).get (by trivial)⟩

#check badPart
#reduce (badPart ()).Dom
#print badPart

theorem bad : False := (badPart ()).get (by trivial)
#print axioms badPart
#print axioms bad
