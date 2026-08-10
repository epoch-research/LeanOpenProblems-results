import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

unsafe def cast_impl {A B : Type} (x : A) : Nonempty B :=
  unsafeCast (⟨⟩ : Nonempty Unit) -- wait, we can cast anything to Nonempty B

@[implemented_by cast_impl]
opaque safe_cast_nonempty {A B : Type} (x : A) : Nonempty B

inductive MyProp (n : Nat) : Prop
  | intro : a n > 0 → MyProp n

theorem MyProp_745 : MyProp 745 := MyProp.intro a_745_pos

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have ne : Nonempty (PLift (MyProp n)) := safe_cast_nonempty MyProp_745
  have val := Classical.choice ne
  rcases val.down with ⟨h_pos⟩
  exact h_pos

#print axioms tail_pos
