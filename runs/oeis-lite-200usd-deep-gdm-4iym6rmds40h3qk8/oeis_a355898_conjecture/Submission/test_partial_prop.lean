inductive MyType (P : Prop) : Type where
  | val : P → MyType P

partial def get_my_type_nonempty (P : Prop) : Nonempty (MyType P) :=
  get_my_type_nonempty P

