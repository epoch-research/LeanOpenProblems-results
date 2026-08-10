inductive Bad (α : Prop) : Nat → Prop
  | mk {n : Nat} : (α → Bad α n) → Bad α (n + 1)

def unsound {α : Prop} {n : Nat} (y : Bad α n) (x : α) : False :=
  match n, y with
  | 0, y => nomatch y
  | _ + 1, .mk f => unsound (f x) x

#print axioms unsound

