inductive U : Prop where
  | base : U
  | mk : (Prop → U) → U

def proj : U → (Prop → U)
  | U.base => fun _ => U.base
  | U.mk f => f
