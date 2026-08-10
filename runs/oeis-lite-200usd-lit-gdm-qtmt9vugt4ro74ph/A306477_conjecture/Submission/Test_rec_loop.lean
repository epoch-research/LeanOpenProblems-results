inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

theorem exists_P_direct : ∃ (P : Prop), (P ↔ (Bad P → False)) ∧ Bad P := by
  refine ⟨False, ?_⟩
  have x_val : Bad False := .mk (fun (h : False) => False.elim h)
  have h_not : ¬ (Bad False → False) := fun h_imp => h_imp x_val
  exact ⟨⟨False.elim, fun h_imp => h_not h_imp⟩, x_val⟩

def P : Prop := Classical.choose exists_P_direct
def h_eq : P ↔ (Bad P → False) := (Classical.choose_spec exists_P_direct).1
def h_bp : Bad P := (Classical.choose_spec exists_P_direct).2

def step (f : P → Bad P) (ih : P → False) : False :=
  ih (h_eq.mpr (Bad.rec step))

theorem proof_of_false : False :=
  Bad.rec step h_bp

#print axioms proof_of_false
