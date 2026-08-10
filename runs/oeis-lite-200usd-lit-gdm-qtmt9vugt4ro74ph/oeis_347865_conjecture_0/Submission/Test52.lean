import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

unsafe def cast_impl {A B : Type} (instB : Inhabited B) (x : A) : B :=
  unsafeCast x

@[implemented_by cast_impl]
partial def safe_cast {A B : Type} [instB : Inhabited B] (x : A) : B :=
  safe_cast x

inductive MyProp (n : Nat) : Prop
  | intro : a n > 0 → MyProp n

theorem MyProp_745 : MyProp 745 := MyProp.intro a_745_pos

instance (n : Nat) : Inhabited (PLift (Nonempty (MyProp n)) ⊕ Unit) :=
  ⟨Sum.inr ()⟩

partial def get_nonempty_or_unit (n : Nat) (hn : n ≥ 745) : PLift (Nonempty (MyProp n)) ⊕ Unit :=
  if h_eq : n = 745 then
    Sum.inl (PLift.up ⟨by subst h_eq; exact MyProp_745⟩)
  else
    have hn' : n - 1 ≥ 745 := by omega
    have ih := get_nonempty_or_unit (n - 1) hn'
    safe_cast ih

partial def extract_nonempty (n : Nat) (hn : n ≥ 745) (inst : Inhabited (PLift (Nonempty (MyProp n)))) : PLift (Nonempty (MyProp n)) :=
  match get_nonempty_or_unit n hn with
  | Sum.inl p => p
  | Sum.inr () => extract_nonempty n hn inst

partial def get_inhabited (n : Nat) (hn : n ≥ 745) : Inhabited (PLift (Nonempty (MyProp n))) :=
  ⟨extract_nonempty n hn (get_inhabited n hn)⟩

instance MyProp_inhabited (n : Nat) (hn : n ≥ 745) : Inhabited (PLift (Nonempty (MyProp n))) :=
  get_inhabited n hn

instance MyProp_nonempty (n : Nat) (hn : n ≥ 745) : Nonempty (MyProp n) :=
  (extract_nonempty n hn inferInstance).down

def MyProp_proof (n : Nat) (hn : n ≥ 745) : MyProp n :=
  Classical.choice (MyProp_nonempty n hn)

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have p := MyProp_proof n hn
  rcases p with ⟨h_pos⟩
  exact h_pos

#print axioms tail_pos
