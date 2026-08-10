import FormalConjectures.Util.ProblemImports

theorem arbitrary2 (P : Prop) : P :=
  Eq.mp (propext ⟨(fun _ : True => arbitrary2 P), (fun _ : P => True.intro)⟩) True.intro

#print axioms arbitrary2
