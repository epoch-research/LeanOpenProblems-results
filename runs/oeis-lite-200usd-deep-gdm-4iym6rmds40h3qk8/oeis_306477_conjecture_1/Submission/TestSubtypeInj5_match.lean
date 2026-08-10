open Classical

def F {α : Type} (f : α → Prop) (Y : Type) (eq : Y = Subtype f) (y : Y) : α :=
  match cast eq y with
  | ⟨val, _⟩ => val
