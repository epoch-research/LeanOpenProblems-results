import FormalConjectures.Util.ProblemImports
axiom bad : False
instance : Inhabited False := ⟨bad⟩
opaque foo : False
#print axioms foo
