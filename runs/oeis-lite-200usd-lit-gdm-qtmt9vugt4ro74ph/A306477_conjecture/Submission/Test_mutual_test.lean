inductive Ind (α : Type) (β : Prop) : Type
  | mk : (β → False) → Ind α β

theorem exists_P : ∃ (P : Prop), P ↔ (Nonempty (Ind Unit P) → False) := by
  by_cases h : Nonempty (Ind Unit False)
  · refine ⟨False, ?_⟩
    have h_not : ¬ (Nonempty (Ind Unit False) → False) := fun h_imp => h_imp h
    exact ⟨False.elim, fun h_imp => h_not h_imp⟩
  · refine ⟨True, ?_⟩
    have h_not_true : ¬ Nonempty (Ind Unit True) := by
      intro h_it
      cases h_it with
      | intro h_it' =>
        match h_it' with
        | .mk f => exact f True.intro
    have h_imp : Nonempty (Ind Unit True) → False := h_not_true
    exact ⟨fun _ => h_imp, fun _ => True.intro⟩

def P : Prop := Classical.choose exists_P
def h_eq : P ↔ (Nonempty (Ind Unit P) → False) := Classical.choose_spec exists_P

mutual
  def not_p (hp : P) : False :=
    have h_ne : Nonempty (Ind Unit P) := ⟨bp⟩
    h_eq.mp hp h_ne

  def bp : Ind Unit P :=
    Ind.mk not_p
end
