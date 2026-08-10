inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def y : Bad True :=
  Bad.mk (fun _ => y)
