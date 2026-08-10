inductive Bad (α : Prop) : Prop
  | mk : (α → False) → Bad α

def Bad' : Prop := Bad Bad'
