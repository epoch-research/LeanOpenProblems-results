import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

unsafe def cast_impl {A B : Type} (instB : Inhabited B) (x : A) : B :=
  unsafeCast x

@[implemented_by cast_impl]
partial def safe_cast {A B : Type} [instB : Inhabited B] (x : A) : B :=
  safe_cast x

inductive MyType (n : Nat) : Type
  | intro : a n > 0 → MyType n

def MyType_745 : MyType 745 := MyType.intro a_745_pos

def inst_745 : Inhabited (PLift (Nonempty (MyType 745))) :=
  ⟨PLift.up ⟨MyType_745⟩⟩

partial def get_inhabited (n : Nat) (hn : n ≥ 745) : Inhabited (PLift (Nonempty (MyType n))) :=
  have inst : Inhabited (Inhabited (PLift (Nonempty (MyType n)))) := ⟨get_inhabited n hn⟩
  @safe_cast _ _ inst inst_745

partial def nonempty_safe (n : Nat) (hn : n ≥ 745) : PLift (Nonempty (MyType n)) :=
  if h_eq : n = 745 then
    PLift.up ⟨by
      subst h_eq
      exact MyType_745⟩
  else
    have hn' : n - 1 ≥ 745 := by omega
    have ih := nonempty_safe (n - 1) hn'
    @safe_cast _ _ (get_inhabited n hn) ih

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have ne := (nonempty_safe n hn).down
  rcases ne with ⟨val⟩
  rcases val with ⟨h_pos⟩
  exact h_pos

#print axioms tail_pos
