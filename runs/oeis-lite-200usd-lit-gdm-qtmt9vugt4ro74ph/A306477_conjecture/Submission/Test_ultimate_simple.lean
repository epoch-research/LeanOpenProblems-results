inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def x_val : Bad False :=
  .mk (fun (h : False) => False.elim h)

theorem h_eq : False ↔ (Bad False → False) := by
  constructor
  · exact False.elim
  · intro h
    exact h x_val

theorem h_eq_prop : False = (Bad False → False) :=
  propext h_eq

theorem proof_of_false : False := by
  have A : Prop := Bad False → False
  have h_eq_A : False = A := h_eq_prop
  have id_A : A → A := id
  have id_cast : A → False := by
    rw [← h_eq_A]
    exact id_A
  have a_val : A := id_cast
  have false_val : False := by
    rw [h_eq_A]
    exact a_val
  exact false_val
