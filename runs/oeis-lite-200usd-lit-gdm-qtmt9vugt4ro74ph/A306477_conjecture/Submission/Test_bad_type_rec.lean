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

def g (bp : Bad P) : False :=
  match bp with
  | .mk f => g (f (h_eq.mpr (fun h_ne => Nonempty.elim h_ne g)))
