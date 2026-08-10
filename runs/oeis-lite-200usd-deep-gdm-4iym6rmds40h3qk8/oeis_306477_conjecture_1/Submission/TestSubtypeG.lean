open Classical

def G {α : Type} (P_choose : α) (Y : Type) (eq : Y = { y : α // y = P_choose }) (y_Y : Y) : α :=
  match cast eq y_Y with
  | ⟨val, _⟩ => val

theorem G_spec {α : Type} (P_choose : α) (Y : Type) (eq : Y = { y : α // y = P_choose }) (y : { y : α // y = P_choose }) :
    G P_choose Y eq (cast eq.symm y) = y.val := by
  cases eq
  rfl
