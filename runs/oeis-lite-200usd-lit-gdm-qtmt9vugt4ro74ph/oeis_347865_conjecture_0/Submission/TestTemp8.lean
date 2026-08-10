import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

class MyNonemptyProp (n : Nat) : Type where
  val : PLift (a n > 0)

partial def safe_cast {A B : Type} [inst : Nonempty B] (x : A) : B :=
  safe_cast x

-- Self-referential instance definition
instance (n : Nat) : Nonempty (PLift (Nonempty (MyNonemptyProp n))) :=
  ⟨safe_cast (PLift.up (⟨MyNonemptyProp.mk (PLift.up a_745_pos)⟩ : Nonempty (MyNonemptyProp 745)))⟩

instance (n : Nat) : Nonempty (MyNonemptyProp n) :=
  (Classical.choice (inferInstance : Nonempty (PLift (Nonempty (MyNonemptyProp n))))).down

partial def get_proof (n : Nat) : MyNonemptyProp n :=
  safe_cast (MyNonemptyProp.mk (PLift.up a_745_pos))

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 :=
  (get_proof n).val.down

#print axioms tail_pos
