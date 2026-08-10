inductive Bad (α : Prop) : Nat → Prop
  | mk {n : Nat} : (α → Bad α n) → Bad α (n + 1)

def unsound {α : Prop} : (n : Nat) → Bad α n → α → False
  | 0, y, _ => nomatch y
  | n + 1, .mk f, x => unsound n (f x) x

mutual
  def g (n : Nat) (bf : Bad False n) : False :=
    match n, bf with
    | 1, bf => unsound 2 (Y ()) bf
    | 0, bf => nomatch bf
    | _ + 2, _ => g 1 (.mk (fun h => False.elim h))

  def Y (u : Unit) : Bad (Bad False 1) 2 :=
    .mk (fun bf => f bf u)

  def f (bf : Bad False 1) (u : Unit) : Bad (Bad False 1) 1 :=
    .mk (fun bf' => False.elim (g 1 bf'))
end

theorem proof_of_false : False :=
  g 1 (.mk (fun h => False.elim h))
