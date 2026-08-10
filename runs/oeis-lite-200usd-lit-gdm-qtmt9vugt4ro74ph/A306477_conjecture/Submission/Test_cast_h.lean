inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def cast_h (F : (Bad False → False) → False) : Bad False → False :=
  fun (y : Bad False) => F (cast_h F)
