inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def bad : T → False
  | T.base => ?_ -- wait, how can we prove False from T.base?
  | T.mk g => bad (g Empty)
