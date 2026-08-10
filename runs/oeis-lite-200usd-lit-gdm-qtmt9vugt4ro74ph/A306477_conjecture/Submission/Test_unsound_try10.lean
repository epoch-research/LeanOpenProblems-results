inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def f (bp : Bad False) : Bad (Bad False) :=
  Bad.mk (fun _ => f bp)
