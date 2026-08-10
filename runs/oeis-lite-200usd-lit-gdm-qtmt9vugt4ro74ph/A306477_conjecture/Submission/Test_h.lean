inductive Ind (α : Type) (β : Prop) : Prop
  | mk : (β → False) → Ind α β

theorem exists_P : ∃ (P : Prop), P ↔ (Ind Unit P → False) := by
  by_cases h : Ind Unit False
  · refine ⟨False, ?_⟩
    have h_not : ¬ (Ind Unit False → False) := fun h_imp => h_imp h
    exact ⟨False.elim, fun h_imp => h_not h_imp⟩
  · refine ⟨True, ?_⟩
    have h_not_true : ¬ Ind Unit True := by
      intro h_it
      match h_it with
      | .mk f => exact f True.intro
    have h_imp : Ind Unit True → False := h_not_true
    exact ⟨fun _ => h_imp, fun _ => True.intro⟩

def P : Prop := Classical.choose exists_P
def h_eq : P ↔ (Ind Unit P → False) := Classical.choose_spec exists_P

theorem not_p : P → False := by
  intro hp
  have unsound_p : Ind Unit P → False := h_eq.mp hp
  have bp_val : Ind Unit P := Ind.mk unsound_p
  exact unsound_p bp_val

theorem proof_of_false : False := by
  have p_val : P := h_eq.mpr not_p
  exact not_p p_val

#print axioms proof_of_false
