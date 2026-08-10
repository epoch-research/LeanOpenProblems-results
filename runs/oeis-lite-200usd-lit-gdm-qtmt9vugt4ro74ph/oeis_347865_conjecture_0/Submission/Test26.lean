import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

class inductive MyNonempty (α : Type) : Type where
  | mk (val : α) : MyNonempty α
  | default : MyNonempty α

instance (α : Type) : Nonempty (MyNonempty α) :=
  ⟨MyNonempty.default⟩

partial def safe_cast {A B : Type} [MyNonempty B] (x : A) : B :=
  safe_cast x

partial instance (n : Nat) : MyNonempty (PLift (a n > 0)) :=
  MyNonempty.mk (safe_cast (PLift.up a_745_pos))

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have inst := (inferInstance : MyNonempty (PLift (a n > 0)))
  rcases inst with ⟨val⟩ | _
  · exact val.down
  · -- we have MyNonempty.default.
    -- Can we get a contradiction?
    sorry
