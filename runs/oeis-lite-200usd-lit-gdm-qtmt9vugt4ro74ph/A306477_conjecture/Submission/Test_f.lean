inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def f {P : Prop} (x : P) : Bad P :=
  .mk (fun (x' : P) => f x')
