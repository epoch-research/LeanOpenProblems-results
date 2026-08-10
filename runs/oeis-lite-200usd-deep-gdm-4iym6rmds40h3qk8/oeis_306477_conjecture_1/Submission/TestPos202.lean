inductive T : Type where
  | base : T
  | mk : (Prop → T) → T

def proj_prop : T → (Prop → T)
  | T.base => fun _ => T.base
  | T.mk f => f

def inj_prop : (Prop → T) → T := T.mk

theorem proj_inj_prop (f : Prop → T) : proj_prop (inj_prop f) = f := rfl
