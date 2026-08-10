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

def unsound_cast : Bad P → (Bad P → False) → False := fun bp x => unsound bp (h_eq.mpr x)

def g (bp_val : Bad P) : False :=
  match bp_val with
  | .mk f_bp =>
    have f_bp_cast : (Bad P → False) → Bad P := fun x => f_bp (h_eq.mpr x)
    have not_a_bp : (Bad P → False) → False := fun a => unsound_cast (f_bp_cast a) a
    not_a_bp g
