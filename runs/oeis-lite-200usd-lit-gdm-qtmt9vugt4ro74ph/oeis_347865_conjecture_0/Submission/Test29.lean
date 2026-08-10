import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

structure MyNonempty (α : Type) : Type where
  val : α

partial def safe_cast {A B : Type} [Nonempty B] (x : A) : B :=
  safe_cast x

partial def get_mynonempty (n : Nat) : MyNonempty (PLift (a n > 0)) :=
  have inst : Nonempty (PLift (a n > 0)) := ⟨(get_mynonempty n).val⟩
  MyNonempty.mk (@safe_cast (PLift (a 745 > 0)) (PLift (a n > 0)) inst (PLift.up a_745_pos))

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 :=
  (get_mynonempty n).val.down

#print axioms tail_pos
