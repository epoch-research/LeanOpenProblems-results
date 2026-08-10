inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def unsound {α : Prop} (y : Bad α) (x : α) : False :=
  match y with
  | .mk f => unsound (f x) x

def x_val : Bad False :=
  .mk (fun (h : False) => False.elim h)

theorem exists_P_direct : ∃ (P : Prop), (P ↔ (Bad P → False)) ∧ Bad P := by
  refine ⟨False, ?_⟩
  have h_not : ¬ (Bad False → False) := fun h_imp => h_imp x_val
  exact ⟨⟨False.elim, fun h_imp => h_not h_imp⟩, x_val⟩

def P : Prop := Classical.choose exists_P_direct
def h_eq : P ↔ (Bad P → False) := (Classical.choose_spec exists_P_direct).1
def h_bp : Bad P := (Classical.choose_spec exists_P_direct).2

theorem h_eq_prop : P = (Bad P → False) := propext h_eq

theorem proof_of_false : False := by
  cases h_bp with
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

#print axioms proof_of_false
