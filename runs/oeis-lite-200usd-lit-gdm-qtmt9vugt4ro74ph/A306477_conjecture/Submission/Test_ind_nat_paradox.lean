inductive Bad (α : Prop) : Nat → Prop
  | mk {n : Nat} : (α → Bad α n) → Bad α (n + 1)

def unsound {α : Prop} {n : Nat} (y : Bad α n) (x : α) : False :=
  match n, y with
  | 0, y => nomatch y
  | _ + 1, .mk f => unsound (f x) x

def x_val : Bad False 1 :=
  .mk (fun (h : False) => False.elim h)

mutual
  def g (bf : Bad False 1) : False :=
    unsound Y bf

  def Y : Bad (Bad False 1) 2 :=
    .mk f

  def f (bf : Bad False 1) : Bad (Bad False 1) 1 :=
    .mk (fun bf' => False.elim (g bf'))
end

theorem proof_of_false : False :=
  g x_val

#print axioms proof_of_false
