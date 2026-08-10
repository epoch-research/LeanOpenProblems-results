inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def unsound {α : Prop} (y : Bad α) (x : α) : False :=
  match y with
  | .mk f => unsound (f x) x

def map {α β : Prop} (h : β → α) (y : Bad α) : Bad β :=
  match y with
  | .mk g => .mk (fun (b : β) => map h (g (h b)))

def x_val : Bad False :=
  .mk (fun (h : False) => False.elim h)

def h_val : (Bad False → False) → False :=
  fun g => g x_val

def y_val : Bad (Bad False → False) :=
  map h_val x_val

abbrev α : Prop := Bad False → False

def step (a : α → Bad α) (ih : α → Bad (Bad False)) : Bad (Bad False) :=
  ih (fun (g : Bad False) => unsound (ih (fun _ => unsound g x_val)) g)
