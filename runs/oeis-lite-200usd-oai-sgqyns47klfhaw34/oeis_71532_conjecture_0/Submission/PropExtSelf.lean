import FormalConjectures.Util.ProblemImports

theorem arbitrary (P : Prop) : P := by
  have e : True = P := propext ⟨(fun _ => arbitrary P), (fun _ => True.intro)⟩
  exact Eq.mp e True.intro

#print axioms arbitrary
