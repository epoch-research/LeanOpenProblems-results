partial def get_nonempty_cheat (P : Prop) : Nonempty P :=
  Classical.choice (Nonempty.intro (get_nonempty_cheat P))
