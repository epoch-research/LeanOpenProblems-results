inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def unsound {α : Prop} (y : Bad α) (x : α) : False :=
  match y with
  | .mk f => unsound (f x) x

theorem exists_P_direct : ∃ (P : Prop), (P ↔ (Bad P → False)) ∧ Bad P := by
  refine ⟨False, ?_⟩
  have x_val : Bad False := .mk (fun (h : False) => False.elim h)
  have h_not : ¬ (Bad False → False) := fun h_imp => h_imp x_val
  exact ⟨⟨False.elim, fun h_imp => h_not h_imp⟩, x_val⟩

def P : Prop := Classical.choose exists_P_direct
def h_eq : P ↔ (Bad P → False) := (Classical.choose_spec exists_P_direct).1
def h_bp : Bad P := (Classical.choose_spec exists_P_direct).2

theorem proof_of_false : False := by
  by_cases hp : P
  · exact (h_eq.mp hp) h_bp
  · have hp_cast : (Bad P → False) → False := fun x => hp (h_eq.mpr x)
    by_cases h_bp_false : Bad P → False
    · exact hp_cast h_bp_false
    · have g : Bad P → False := fun bp' => unsound bp' (h_eq.mpr h_bp_false)
      exact h_bp_false g
