inductive Bad (α : Prop) : Type
  | mk : (α → Bad α) → Bad α

def unsound {α : Prop} (y : Bad α) (x : α) : False :=
  match y with
  | .mk f => unsound (f x) x

def map {α β : Prop} (h : β → α) (y : Bad α) : Bad β :=
  match y with
  | .mk g => .mk (fun (b : β) => map h (g (h b)))

theorem exists_P : ∃ (P : Prop), P ↔ (Nonempty (Bad P) → False) := by
  by_cases h : Nonempty (Bad False)
  · refine ⟨False, ?_⟩
    have h_not : ¬ (Nonempty (Bad False) → False) := fun h_imp => h_imp h
    exact ⟨False.elim, fun h_imp => h_not h_imp⟩
  · refine ⟨True, ?_⟩
    have h_not_true : ¬ Nonempty (Bad True) := by
      intro h_bt
      cases h_bt with
      | intro h_bt' =>
        have h_bf : Bad False := map (fun (f : False) => True.intro) h_bt'
        exact h ⟨h_bf⟩
    have h_imp : Nonempty (Bad True) → False := h_not_true
    exact ⟨fun _ => h_imp, fun _ => True.intro⟩


theorem exists_P_direct : ∃ (P : Prop), (P ↔ (Nonempty (Bad P) → False)) ∧ Nonempty (Bad P) := by
  refine ⟨False, ?_⟩
  have x_val : Bad False := .mk (fun h => False.elim h)
  have h_not : ¬ (Nonempty (Bad False) → False) := fun h_imp => h_imp ⟨x_val⟩
  exact ⟨⟨False.elim, fun h_imp => h_not h_imp⟩, ⟨x_val⟩⟩

def P : Prop := Classical.choose exists_P_direct
def h_eq : P ↔ (Nonempty (Bad P) → False) := (Classical.choose_spec exists_P_direct).1
def h_bp : Nonempty (Bad P) := (Classical.choose_spec exists_P_direct).2
def h_eq_prop : P = (Nonempty (Bad P) → False) := propext h_eq


