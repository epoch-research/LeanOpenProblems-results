open Classical

def F_sigma {α : Type} (p : α → Prop) (Y : Type) (eq : (Σ y : α, PLift (p y)) = Y) (y : Y) : α :=
  (cast eq.symm y).fst

theorem F_sigma_spec {α : Type} (p : α → Prop) (Y : Type) (eq : (Σ y : α, PLift (p y)) = Y) (y : Σ y : α, PLift (p y)) :
    F_sigma p Y eq (cast eq y) = y.fst := by
  cases eq
  rfl
