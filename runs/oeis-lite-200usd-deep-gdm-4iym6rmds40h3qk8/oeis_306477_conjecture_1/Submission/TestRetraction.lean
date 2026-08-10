inductive T : Prop where
  | base : T
  | mk : (Prop → T) → T

def proj : T → (Prop → T)
  | T.base => fun _ => T.base
  | T.mk f => f

theorem proj_mk (f : Prop → T) : proj (T.mk f) = f := rfl

def inj_P (h : T → Prop) : Prop := h T.base

def proj_P (p : Prop) : T → Prop := fun _ => p

theorem proj_inj_P (h : T → Prop) : proj_P (inj_P h) = h := by
  ext t
  dsimp [proj_P, inj_P]
  have h_eq : T.base = t := rfl
  rw [h_eq]
