inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def e : T → Type
  | T.base => Empty
  | T.mk f => (X : Type) × (e (f X))
