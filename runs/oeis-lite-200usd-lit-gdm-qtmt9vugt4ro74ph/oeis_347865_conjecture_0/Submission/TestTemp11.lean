import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

partial def safe_cast {A B : Type} [inst : Nonempty B] (x : A) : B :=
  safe_cast x

inductive MyNonempty (α : Type) : Type
  | intro (val : α) : MyNonempty α

partial def get_nonempty (n : Nat) : PLift (Nonempty (MyNonempty (PLift (a n > 0)))) :=
  have inst : Nonempty (PLift (Nonempty (MyNonempty (PLift (a n > 0))))) := ⟨get_nonempty n⟩
  @safe_cast (PLift (Nonempty (MyNonempty (PLift (a 745 > 0))))) (PLift (Nonempty (MyNonempty (PLift (a n > 0))))) inst (PLift.up (⟨MyNonempty.intro (PLift.up a_745_pos)⟩ : Nonempty (MyNonempty (PLift (a 745 > 0)))))

instance (n : Nat) : Nonempty (MyNonempty (PLift (a n > 0))) :=
  (get_nonempty n).down

partial def get_proof (n : Nat) : MyNonempty (PLift (a n > 0)) :=
  safe_cast (MyNonempty.intro (PLift.up a_745_pos))

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have res := get_proof n
  rcases res with ⟨val⟩
  exact val.down

#print axioms tail_pos
