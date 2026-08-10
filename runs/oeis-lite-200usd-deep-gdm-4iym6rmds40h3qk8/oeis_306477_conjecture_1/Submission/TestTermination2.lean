inductive T : Type 1 where
  | mk2 : (Prop → T) → T

def bad : T → False
  | T.mk2 f => bad (f False)
