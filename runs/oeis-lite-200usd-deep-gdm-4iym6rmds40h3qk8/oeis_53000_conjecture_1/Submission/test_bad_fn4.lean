inductive Bad2 : Type 1
| mk1 : (Type 0 → Bad2) → Bad2

mutual
  def bad_fn (u : Unit) : Bad2 :=
    Bad2.mk1 (fun _ => bad_fn u)
end
