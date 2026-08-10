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
def h_eq_prop : P = (Bad P → False) := propext h_eq

theorem proof_of_false : False := by
  by_cases hp : P
  · exact (h_eq.mp hp) h_bp
  · cases h_bp with
    | mk f =>
      have f_cast : (Bad P → False) → Bad P := by
        rw [h_eq_prop] at f
        exact f
      have unsound_cast : Bad P → (Bad P → False) → False := by
        rw [h_eq_prop] at unsound
        exact unsound
      have hp_cast : (Bad P → False) → False := by
        rw [h_eq_prop] at hp
        exact hp
      by_cases h_bp_false : Bad P → False
      · exact hp_cast h_bp_false
      · have bp : Bad P := by
          by_contra h_not_bp
          exact h_bp_false h_not_bp
        let g : Bad P → False := unsound_cast bp
        exact unsound_cast (f_cast g) g

#print axioms proof_of_false
