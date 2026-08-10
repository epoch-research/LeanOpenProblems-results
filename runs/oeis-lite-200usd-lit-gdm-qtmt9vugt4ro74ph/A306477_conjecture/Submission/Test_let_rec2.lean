inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def unsound {α : Prop} (y : Bad α) (x : α) : False :=
  match y with
  | .mk f => unsound (f x) x

def x_val : Bad False :=
  .mk (fun (h : False) => False.elim h)

theorem h_eq_prop : False = (Bad False → False) := by
  apply propext
  constructor
  · intro h; exact False.elim h
  · intro h_imp; exact h_imp x_val

theorem proof_of_false : False := by
  let rec g (bp : Bad False) : False := by
    have y_cast : Bad (Bad False → False) := cast (congrArg Bad h_eq_prop) bp
    have unsound_bp : (Bad False → False) → False := unsound y_cast
    exact unsound_bp (fun bp' => unsound (cast (congrArg Bad h_eq_prop) bp') g)
  exact g x_val
