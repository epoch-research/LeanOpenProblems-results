inductive T : Type 1 where
  | mk : (Type → T) → T

def T_to_prop : T → Prop
  | T.mk f => T_to_prop (f Empty)
