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
  cases h_bp with
  | mk f =>
    have f_cast : (Bad P → False) → Bad P :=
      fun (x : Bad P → False) => f (cast h_eq_prop.symm x)
    have unsound_cast : Bad P → (Bad P → False) → False :=
      fun (bp' : Bad P) (x : Bad P → False) => unsound bp' (cast h_eq_prop.symm x)
    have not_x : (Bad P → False) → False :=
      fun (x : Bad P → False) => unsound_cast (f_cast x) x
    have bp_witness : Bad P := f_cast not_x
    exact unsound_cast bp_witness not_x

#print axioms proof_of_false
