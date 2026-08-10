inductive Bad (α : Prop) : Type
  | mk : (α → Bad α) → Bad α

def unsound {α : Prop} (y : Bad α) (x : α) : False :=
  match y with
  | .mk f => unsound (f x) x

theorem exists_P_direct : ∃ (P : Prop), (P ↔ (Nonempty (Bad P) → False)) ∧ Nonempty (Bad P) := by
  refine ⟨False, ?_⟩
  have x_val : Bad False := .mk (fun h => False.elim h)
  have h_not : ¬ (Nonempty (Bad False) → False) := fun h_imp => h_imp ⟨x_val⟩
  exact ⟨⟨False.elim, fun h_imp => h_not h_imp⟩, ⟨x_val⟩⟩

def P : Prop := Classical.choose exists_P_direct
def h_eq : P ↔ (Nonempty (Bad P) → False) := (Classical.choose_spec exists_P_direct).1
def h_bp : Nonempty (Bad P) := (Classical.choose_spec exists_P_direct).2
def h_eq_prop : P = (Nonempty (Bad P) → False) := propext h_eq

theorem proof_of_false : False := by
  cases h_bp with
  | intro bp =>
    have not_a_2 : (Nonempty (Bad P) → False) → False := cast (congrArg (fun X => X → False) h_eq_prop) (unsound bp)
    cases bp with
    | mk f =>
      have f_cast : (Nonempty (Bad P) → False) → Bad P := fun x => f (h_eq.mpr x)
      have not_a : (Nonempty (Bad P) → False) → False := fun a => a ⟨f_cast a⟩
      have not_p : P → False := cast (congrArg (fun X => X → False) h_eq_prop).symm not_a

      exact unsound bp (h_eq.mpr not_a)
