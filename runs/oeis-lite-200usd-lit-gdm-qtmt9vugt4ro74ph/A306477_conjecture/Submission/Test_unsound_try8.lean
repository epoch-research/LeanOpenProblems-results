inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def y_fn : Nat → Bad True
  | 0 => Bad.mk (fun _ => y_fn 0)
  | n + 1 => Bad.mk (fun _ => y_fn n)
