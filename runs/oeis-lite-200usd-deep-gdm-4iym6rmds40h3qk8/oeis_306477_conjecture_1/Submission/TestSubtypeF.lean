open Classical

def F {α : Type} (P : α) (Y : Type) (eq : { y : α // y = P } = Y) (y_Y : Y) : α :=
  (cast eq.symm y_Y).val

theorem F_spec {α : Type} (P : α) (Y : Type) (eq : { y : α // y = P } = Y) (y : { y : α // y = P }) :
    F P Y eq (cast eq y) = y.val := by
  cases eq
  rfl
