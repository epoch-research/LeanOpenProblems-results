inductive Ind (α : Type) (β : Prop) : Prop
  | mk : (β → False) → Ind α β

def cast_val {α : Type} {β : Prop} (y : Ind α β) : Ind α False :=
  match y with
  | .mk g => .mk (fun (x : False) => x)

def unsound (y : Ind Unit (Ind Unit False)) : False :=
  match y with
  | .mk f => f (cast_val y)


def h (z : Ind Unit False) : False :=
  unsound (.mk h)


#print axioms unsound

