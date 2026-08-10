import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

partial def safe_cast {A B : Type} [inst : Nonempty B] (x : A) : B :=
  safe_cast x

instance (n : Nat) : Nonempty (PLift (a n > 0) ⊕ (PLift (a n > 0) → False)) := by
  by_cases h : a n > 0
  · exact ⟨Sum.inl (PLift.up h)⟩
  · exact ⟨Sum.inr (fun x => h x.down)⟩

partial def get_nonempty (n : Nat) : PLift (a n > 0) ⊕ (PLift (a n > 0) → False) :=
  @safe_cast (PLift (a 745 > 0) ⊕ (PLift (a 745 > 0) → False)) (PLift (a n > 0) ⊕ (PLift (a n > 0) → False)) (inferInstance) (Sum.inl (PLift.up a_745_pos))

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have res := get_nonempty n
  rcases res with val | val_false
  · exact val.down
  · sorry

#print axioms tail_pos
