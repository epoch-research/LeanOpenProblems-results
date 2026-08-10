import Mathlib

inductive MyType (P : Prop) : Type where
  | inl : Nonempty P → MyType P
  | inr : (Nonempty P → False) → MyType P

partial def get_proof (P : Prop) (d : MyType P) (d2 : MyType (Nonempty P)) : Nonempty P :=
  match d with
  | MyType.inl hp => hp
  | MyType.inr hnp =>
    match d2 with
    | MyType.inl hq => False.elim (hnp (Classical.choice hq))
    | MyType.inr hnq => get_proof P d d2
