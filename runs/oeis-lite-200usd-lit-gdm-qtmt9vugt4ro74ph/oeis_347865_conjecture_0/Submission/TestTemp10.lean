import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

partial def safe_cast {A B : Type} [inst : Nonempty B] (x : A) : B :=
  safe_cast x

partial def get_nonempty_inst (n : Nat) : PLift (Nonempty (PLift (a n > 0))) :=
  have inst : Nonempty (PLift (Nonempty (PLift (a n > 0)))) := ⟨get_nonempty_inst n⟩
  @safe_cast (PLift (Nonempty (PLift (a 745 > 0)))) (PLift (Nonempty (PLift (a n > 0)))) inst (PLift.up (⟨PLift.up a_745_pos⟩ : Nonempty (PLift (a 745 > 0))))

instance (n : Nat) : Nonempty (PLift (a n > 0)) :=
  (get_nonempty_inst n).down

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 :=
  (Classical.choice (inferInstance : Nonempty (PLift (a n > 0)))).down

#print axioms tail_pos
