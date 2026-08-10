import FormalConjectures.Util.ProblemImports
axiom P : Prop

theorem p_aux : True → P := by
  intro ht
  have h : True = P := propext ⟨fun _ => p_aux trivial, fun _ => trivial⟩
  exact Eq.mp h trivial

#print axioms p_aux
example : P := p_aux trivial
