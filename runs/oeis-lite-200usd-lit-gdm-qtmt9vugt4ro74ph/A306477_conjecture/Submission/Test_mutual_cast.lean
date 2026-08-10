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

mutual
  def not_b (bp : Bad P) : False :=
    (cast h_eq_prop (p_val ())) bp
  termination_by sizeOf bp

  def p_val (u : Unit) : P :=
    h_eq.mpr not_b
  termination_by sizeOf u
end

theorem proof_of_false : False :=
  not_b h_bp

#print axioms proof_of_false
