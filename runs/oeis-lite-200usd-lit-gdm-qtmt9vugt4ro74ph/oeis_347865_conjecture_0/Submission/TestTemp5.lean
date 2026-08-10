import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

partial def safe_cast {A B : Type} [inst : Nonempty B] (x : A) : B :=
  safe_cast x

partial def get_nonempty_instance (n : Nat) : Nonempty (PLift (a n > 0) ⊕ PLift (PLift (a 745 > 0) → False)) :=
  ⟨@safe_cast (PLift (a 745 > 0) ⊕ PLift (PLift (a 745 > 0) → False)) (PLift (a n > 0) ⊕ PLift (PLift (a 745 > 0) → False)) (get_nonempty_instance n) (Sum.inl (PLift.up a_745_pos))⟩

instance (n : Nat) : Nonempty (PLift (a n > 0) ⊕ PLift (PLift (a 745 > 0) → False)) :=
  get_nonempty_instance n

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have res : PLift (a n > 0) ⊕ PLift (PLift (a 745 > 0) → False) := @safe_cast (PLift (a 745 > 0) ⊕ PLift (PLift (a 745 > 0) → False)) (PLift (a n > 0) ⊕ PLift (PLift (a 745 > 0) → False)) (inferInstance) (Sum.inl (PLift.up a_745_pos))
  rcases res with val | val_false
  · exact val.down
  · have f : PLift (a 745 > 0) → False := val_false.down
    exfalso
    exact f (PLift.up a_745_pos)

#print axioms tail_pos
