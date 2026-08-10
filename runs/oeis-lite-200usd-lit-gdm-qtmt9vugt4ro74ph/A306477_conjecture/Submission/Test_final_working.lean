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

theorem proof_of_false : False := by
  have step (f : P → Bad P) (ih : P → False) : False := by
    have g : Bad P → False := fun bp' =>
      ih (h_eq.mpr (fun bp'' => unsound bp'' (h_eq.mpr ih)))
    exact ih (h_eq.mpr g)
  exact Bad.rec (motive := fun _ => False) step h_bp

#print axioms proof_of_false
