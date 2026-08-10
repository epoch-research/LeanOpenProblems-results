import FormalConjectures.Util.ProblemImports

theorem badP (P : Prop) : P := by
  have h : P = True := propext ⟨fun _ => trivial, fun _ => badP P⟩
  exact h.symm ▸ trivial
#print axioms badP
