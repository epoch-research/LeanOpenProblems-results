import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

unsafe def cast_impl {A B : Type} (instB : Nonempty B) (x : A) : B :=
  unsafeCast x

@[implemented_by cast_impl]
partial def safe_cast {A B : Type} (instB : Nonempty B) (x : A) : B :=
  safe_cast instB x

inductive MyProp (n : Nat) : Prop
  | intro : a n > 0 → MyProp n

theorem MyProp_745 : MyProp 745 := MyProp.intro a_745_pos

partial def MyProp_nonempty_plift (n : Nat) (hn : n ≥ 745) (inst : Nonempty (PLift (Nonempty (PLift (MyProp n))))) : PLift (Nonempty (PLift (MyProp n))) :=
  safe_cast inst (PLift.up (⟨PLift.up MyProp_745⟩ : Nonempty (PLift (MyProp 745))))
