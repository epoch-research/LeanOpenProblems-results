inductive Bad : Type 1
| mk1 : (Prop → Bad) → Bad
| mk2 : Bad

instance : Inhabited Bad where
  default := Bad.mk2

partial def f_rec (p : Prop) : Bad := Bad.mk1 (fun _ => f_rec p)
