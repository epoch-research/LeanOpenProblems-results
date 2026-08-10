inductive MyType : Prop → Type
  | mk (p : Prop) : MyType (p → False) → MyType p
  | base : MyType True

#check MyType.rec




