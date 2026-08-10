import FormalConjectures.Util.ProblemImports

noncomputable def badPart : Part Empty := ⟨True, fun _ => badPart.get trivial⟩

theorem badEmpty : Empty := badPart.get trivial
theorem bad : False := nomatch badEmpty
#print axioms badPart
#print axioms bad
