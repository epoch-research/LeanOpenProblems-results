inductive T : Type 1 where
  | mk : (Type → T) → T

partial def g (X : Type) : T := T.mk g
