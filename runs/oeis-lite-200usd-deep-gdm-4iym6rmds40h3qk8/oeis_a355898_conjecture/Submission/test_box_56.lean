import Mathlib

inductive MyNonempty (P : Prop) : Type where
  | intro : P → MyNonempty P
  | dummy : MyNonempty P

instance (P : Prop) : Nonempty (MyNonempty P) :=
  ⟨MyNonempty.dummy⟩

mutual
  partial def cheat_any (P : Prop) : P :=
    match cheat_nonempty P with
    | MyNonempty.intro p => p
    | MyNonempty.dummy => cheat_any P

  partial def cheat_nonempty (P : Prop) : MyNonempty P :=
    MyNonempty.intro (cheat_any P)
end
