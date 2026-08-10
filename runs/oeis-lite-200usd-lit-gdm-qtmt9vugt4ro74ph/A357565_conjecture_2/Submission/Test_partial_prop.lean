import FormalConjectures.Util.ProblemImports

inductive MyType (P : Prop) where
  | mk1 : MyType P
  | mk2 : P → MyType P
deriving Nonempty

partial def my_val (P : Prop) : MyType P :=
  my_val P

theorem use_my_val (P : Prop) : MyType P := my_val P

#print axioms use_my_val
