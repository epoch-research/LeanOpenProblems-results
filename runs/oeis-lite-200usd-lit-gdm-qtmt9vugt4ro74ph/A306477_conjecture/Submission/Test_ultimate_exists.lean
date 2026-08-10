inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def unsound {α : Prop} (y : Bad α) (x : α) : False :=
  match y with
  | .mk f => unsound (f x) x

def map {α β : Prop} (h : β → α) (y : Bad α) : Bad β :=
  match y with
  | .mk g => .mk (fun (b : β) => map h (g (h b)))

theorem exists_P : ∃ (P : Prop), P ↔ (Bad P → False) := by
  by_cases h : Bad False
  · refine ⟨False, ?_⟩
    have h_not : ¬ (Bad False → False) := by
      intro h_imp
      exact h_imp h
    exact ⟨False.elim, fun h_imp => h_not h_imp⟩
  · refine ⟨True, ?_⟩
    have h_not_true : ¬ Bad True := by
      intro h_bt
      have h_bf : Bad False := map (fun (f : False) => True.intro) h_bt
      exact h h_bf
    have h_imp : Bad True → False := fun h_bt => h_not_true h_bt
    exact ⟨fun _ => h_imp, fun _ => True.intro⟩

def P : Prop := Classical.choose exists_P
def h_eq : P ↔ (Bad P → False) := Classical.choose_spec exists_P
theorem h_eq_prop : P = (Bad P → False) := propext h_eq

theorem proof_of_false : False := by
  by_cases h_bp : Bad P
  · cases h_bp with
    | mk f =>
      -- f has type P → Bad P
      have f_cast : (Bad P → False) → Bad P := by
        rw [← h_eq_prop]
        exact f
      have unsound_cast : Bad P → (Bad P → False) → False := by
        rw [← h_eq_prop]
        exact unsound
      have not_a : (Bad P → False) → False := fun a =>
        unsound_cast (f_cast a) a
      have p_val : P := by
        rw [h_eq_prop]
        exact not_a
      exact not_a p_val
  · have h_not_bp : Bad P → False := h_bp
    have p_val : P := h_eq.mpr h_not_bp
    have bp_val : Bad P := Bad.mk (fun (p : P) => False.elim (not_a p)) -- wait, not_a is not in scope here
    sorry
