import FormalConjectures.Util.ProblemImports

inductive MyType (P : Prop) where
  | mk1 : MyType P
  | mk2 : P → MyType P
deriving Nonempty

partial def extract (P : Prop) : MyType P → P
  | MyType.mk1 => extract P MyType.mk1
  | MyType.mk2 p => p


def my_proof (P : Prop) : P := extract P MyType.mk1
