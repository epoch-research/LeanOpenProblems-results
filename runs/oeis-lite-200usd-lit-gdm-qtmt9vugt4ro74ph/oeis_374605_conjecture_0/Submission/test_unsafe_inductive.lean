inductive MyType : Prop → Prop
  | mk (p : Prop) : MyType (p → False) → MyType p

def t_any (p : Prop) : MyType p :=
  MyType.mk p (t_any (p → False))

