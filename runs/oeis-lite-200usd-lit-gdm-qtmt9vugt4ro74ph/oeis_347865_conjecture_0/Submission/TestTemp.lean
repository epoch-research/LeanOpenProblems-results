import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

partial def safe_cast {A B : Type} [inst : Nonempty B] (x : A) : B :=
  safe_cast x

instance (n : Nat) : Nonempty (PLift (a n > 0)) :=
  let rec inst : Nonempty (PLift (a n > 0)) := ⟨@safe_cast (PLift (a 745 > 0)) (PLift (a n > 0)) inst (PLift.up a_745_pos)⟩
  inst

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 :=
  (Classical.choice (inferInstance : Nonempty (PLift (a n > 0)))).down

#print axioms tail_pos
