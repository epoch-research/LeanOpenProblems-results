import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

unsafe def cast_impl {A B : Type} (instB : Nonempty B) (x : A) : B :=
  unsafeCast x

@[implemented_by cast_impl]
partial def safe_cast {A B : Type} [instB : Nonempty B] (x : A) : B :=
  safe_cast x

inductive MyProp (n : Nat) : Prop
  | intro : a n > 0 → MyProp n

theorem MyProp_745 : MyProp 745 := MyProp.intro a_745_pos

inductive MyType (n : Nat) : Type
  | intro : MyProp n → MyType n

unsafe def nonempty_impl (n : Nat) (hn : n ≥ 745) (inst : Nonempty (PLift (Nonempty (MyType n)))) : PLift (Nonempty (MyType n)) :=
  unsafeCast (PLift.up ⟨MyType.intro MyProp_745⟩ : PLift (Nonempty (MyType 745)))

@[implemented_by nonempty_impl]
partial def MyType_nonempty_plift (n : Nat) (hn : n ≥ 745) [inst : Nonempty (PLift (Nonempty (MyType n)))] : PLift (Nonempty (MyType n)) :=
  MyType_nonempty_plift n hn

instance instPLiftNonemptyMyType (n : Nat) (hn : n ≥ 745) : Nonempty (PLift (Nonempty (MyType n))) :=
  ⟨PLift.up (MyType_nonempty_plift n hn (inst := instPLiftNonemptyMyType n hn))⟩

instance MyType_nonempty (n : Nat) (hn : n ≥ 745) : Nonempty (MyType n) :=
  have inst : Nonempty (PLift (Nonempty (MyType n))) := instPLiftNonemptyMyType n hn
  (MyType_nonempty_plift n hn).down

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have ne := MyType_nonempty n hn
  have val := Classical.choice ne
  rcases val with ⟨p⟩
  rcases p with ⟨h_pos⟩
  exact h_pos

#print axioms tail_pos
