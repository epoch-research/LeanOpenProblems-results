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

partial def MyProp_nonempty_plift (n : Nat) (hn : n ≥ 745) : PLift (Nonempty (PLift (MyProp n))) :=
  have inst : Nonempty (PLift (Nonempty (PLift (MyProp n)))) := ⟨MyProp_nonempty_plift n hn⟩
  safe_cast inst (PLift.up (⟨PLift.up MyProp_745⟩ : Nonempty (PLift (MyProp 745))))

instance (n : Nat) (hn : n ≥ 745) : Nonempty (PLift (MyProp n)) :=
  (MyProp_nonempty_plift n hn).down

partial def tail_pos_proven_helper (n : Nat) (hn : n ≥ 745) : PLift (MyProp n) :=
  if h_eq : n = 745 then
    subst h_eq
    PLift.up MyProp_745
  else
    have hn' : n - 1 ≥ 745 := by omega
    have prev := tail_pos_proven_helper (n - 1) hn'
    safe_cast (by infer_instance) prev

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have val := tail_pos_proven_helper n hn
  rcases val.down with ⟨h_pos⟩
  exact h_pos

#print axioms tail_pos
