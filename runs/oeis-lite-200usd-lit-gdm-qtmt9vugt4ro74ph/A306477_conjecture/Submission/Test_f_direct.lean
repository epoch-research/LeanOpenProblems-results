inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def f (y : Bad False) : Bad (Bad False) :=
  .mk f
