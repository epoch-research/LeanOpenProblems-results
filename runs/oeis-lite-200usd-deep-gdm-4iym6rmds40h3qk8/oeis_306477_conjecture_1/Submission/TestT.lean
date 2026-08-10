inductive T : Type 1 where
  | mk : (Type → T) → T

def t : Type → T
  | α => T.mk t
