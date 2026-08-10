import FormalConjectures.Util.ProblemImports

theorem foo : False := by
  have h : True = False := propext ⟨fun _ => foo, fun f => trivial⟩
  exact Eq.mp h trivial
#print axioms foo
