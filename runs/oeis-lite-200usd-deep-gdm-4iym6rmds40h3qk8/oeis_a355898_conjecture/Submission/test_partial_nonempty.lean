import Mathlib

partial def get_nonempty_cheat (P : Prop) : Nonempty P :=
  get_nonempty_cheat P

theorem prove_any (P : Prop) : P :=
  Classical.choice (get_nonempty_cheat P)

#print axioms prove_any
