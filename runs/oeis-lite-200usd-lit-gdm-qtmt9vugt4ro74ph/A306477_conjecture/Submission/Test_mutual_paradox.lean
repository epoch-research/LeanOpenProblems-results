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

mutual
  def Y (u : Unit) : Bad (Bad False) := .mk (f u)
  def f (u : Unit) (bf : Bad False) : Bad (Bad False) := map (h u) bf
  def h (u : Unit) (bf : Bad False) : False := unsound (Y u) bf
end

theorem proof_of_false : False :=
  h () x_val

#print axioms proof_of_false
