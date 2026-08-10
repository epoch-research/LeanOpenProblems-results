import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

partial def safe_cast {A B : Type} [inst : Nonempty B] (x : A) : B :=
  safe_cast x

instance (n : Nat) : Nonempty (PLift (a n > 0) ⊕ PLift (PLift (a 745 > 0) → False)) :=
  ⟨safe_cast (Sum.inl (PLift.up a_745_pos) : PLift (a 745 > 0) ⊕ PLift (PLift (a 745 > 0) → False))⟩

#print axioms a_745_pos
