inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def y_bf : Bad False := .mk (fun (f : False) => False.elim f)

theorem exists_P_direct : ∃ (P : Prop), P ↔ (Bad P → False) := by
  refine ⟨False, ?_⟩
  have h_not : ¬ (Bad False → False) := by
    intro h_imp
    exact h_imp y_bf
  exact ⟨False.elim, fun h_imp => h_not h_imp⟩
