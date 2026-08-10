inductive T : Type 1 where
  | mk : (Type → T) → T

def bad : T → False
  | T.mk g => bad (g Empty)
