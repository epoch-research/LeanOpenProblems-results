inductive T : Type 1 where
  | mk : (Type → T) → T

def T_to_False : T → False
  | T.mk f => T_to_False (f Empty)
