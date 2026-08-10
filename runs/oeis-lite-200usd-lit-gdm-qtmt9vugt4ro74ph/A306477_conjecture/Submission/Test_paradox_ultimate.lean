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

def Y_triple : Bad (Bad (Bad False)) :=
  map unsound y_val

def Y_double_to_false : Bad (Bad False) → False :=
  unsound Y_triple

def Y_double : Bad (Bad False) :=
  map (map unsound) Y_triple

def proof_of_false : False :=
  Y_double_to_false Y_double

#print axioms proof_of_false
