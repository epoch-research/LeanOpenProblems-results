inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def unsound {α : Prop} (y : Bad α) (x : α) : False :=
  match y with
  | .mk f => unsound (f x) x

def x_val : Bad False :=
  .mk (fun (h : False) => False.elim h)

theorem h_eq : False ↔ (Bad False → False) := by
  constructor
  · exact False.elim
  · intro h; exact h x_val

theorem proof_of_false : False := by
  let rec not_a (bp : Bad False) : False :=
    unsound bp (h_eq.mpr not_a)
  exact not_a x_val
