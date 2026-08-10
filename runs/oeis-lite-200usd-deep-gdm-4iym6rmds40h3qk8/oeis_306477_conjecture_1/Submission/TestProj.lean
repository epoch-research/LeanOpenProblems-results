inductive T : Prop where
  | base : T
  | mk : (Prop → T) → T

def proj : T → (Prop → T)
  | T.base => fun _ => T.base
  | T.mk f => f

theorem proj_mk (f : Prop → T) : proj (T.mk f) = f := rfl
