inductive Opt (p : Prop) : Type where
  | none : Opt p
  | some : p → Opt p

def get_val {p : Prop} : (o : Opt p) → (o ≠ Opt.none) → p
  | Opt.some x, _ => x
  | Opt.none, h => False.elim (h rfl)
