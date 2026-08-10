inductive Bad (α : Prop) : Nat → Prop
  | mk {n : Nat} : (α → Bad α n) → Bad α (n + 1)

def unsound {α : Prop} : (n : Nat) → Bad α n → α → False
  | 0, y, x => nomatch y
  | n + 1, .mk f, x => unsound n (f x) x

mutual
  def g : (n : Nat) → Bad False n → False
    | 1, bf => unsound 2 (Y 2) bf
    | _, _ => False.elim

  def Y : (n : Nat) → Bad (Bad False 1) n
    | 2 => .mk (f 1)
    | _ => .mk (fun _ => Y 0)

  def f : (n : Nat) → Bad False 1 → Bad (Bad False 1) n
    | 1, bf => .mk (fun bf' => False.elim (g 1 bf'))
    | _ => .mk (fun _ => Y 0)
end

theorem proof_of_false : False :=
  g 1 (.mk (fun h => False.elim h))
