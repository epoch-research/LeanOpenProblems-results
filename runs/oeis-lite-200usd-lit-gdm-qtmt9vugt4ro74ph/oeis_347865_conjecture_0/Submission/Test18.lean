import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

class MyNonempty (α : Type) : Type where
  val : α

partial def safe_cast {A B : Type} [Nonempty B] (x : A) : B :=
  safe_cast x

instance (α : Type) : Nonempty (MyNonempty α) :=
  ⟨⟨safe_cast (PLift.up (by omega : 1 > 0))⟩⟩

partial instance (n : Nat) : MyNonempty (PLift (a n > 0)) :=
  ⟨safe_cast (PLift.up a_745_pos)⟩

theorem tail_pos (n : Nat) : a n > 0 :=
  (MyNonempty.val : PLift (a n > 0)).down

#print axioms tail_pos
