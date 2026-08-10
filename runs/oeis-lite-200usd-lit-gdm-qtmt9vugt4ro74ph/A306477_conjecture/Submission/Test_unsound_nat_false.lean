inductive Bad (α : Prop) : Nat → Prop
  | zero : Bad α 0
  | mk {n : Nat} : (α → Bad α n) → Bad α (n + 1)

def unsound {n : Nat} (y : Bad False n) (x : False) : False :=
  match y with
  | .zero => False.elim x
  | .mk f => unsound (f x) x
