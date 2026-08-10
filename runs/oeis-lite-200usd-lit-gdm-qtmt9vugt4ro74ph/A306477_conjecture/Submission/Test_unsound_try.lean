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

-- Let's define h_val
def h_val : (Bad False → False) → False :=
  fun g => g x_val

-- def g (y : Bad False) : False :=
--   unsound (map h_val y) g

-- def proof_of_false : False :=
--   g x_val


#check @Bad.rec

