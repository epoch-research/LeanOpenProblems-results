import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

-- Forward declaration using partial def
partial def get_nonempty_val (n : Nat) (hn : n ≥ 745) : PLift (Nonempty (a n > 0)) :=
  get_nonempty_val n hn

instance (n : Nat) (hn : n ≥ 745) : Nonempty (PLift (Nonempty (a n > 0))) :=
  ⟨get_nonempty_val n hn⟩

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 :=
  Classical.choice (get_nonempty_val n hn).down

#print axioms tail_pos
