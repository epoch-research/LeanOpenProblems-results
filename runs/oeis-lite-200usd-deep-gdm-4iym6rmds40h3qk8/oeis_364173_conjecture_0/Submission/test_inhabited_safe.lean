import FormalConjectures.Util.ProblemImports

variable (P : Prop)

theorem my_nonempty : Nonempty (P ⊕ (P → False)) := by
  by_cases hP : P
  · exact ⟨Sum.inl hP⟩
  · exact ⟨Sum.inr hP⟩

noncomputable def my_val : P ⊕ (P → False) := Classical.choice (my_nonempty P)

noncomputable instance my_inst : Inhabited (P ⊕ (P → False)) := ⟨my_val P⟩

opaque my_opaque : P ⊕ (P → False)

#print axioms my_opaque
