inductive U : Prop where
  | base : U
  | mk : (Prop → U) → U

def not_U : U → U
  | U.base => U.mk (fun _ => U.base)
  | U.mk _ => U.base
