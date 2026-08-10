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

inductive MyType (n : Nat) : Type
  | intro : MyProp n → MyType n

instance (n : Nat) : Inhabited (PLift (Nonempty (MyType n)) ⊕ Unit) :=
  ⟨Sum.inr ()⟩

instance (n : Nat) : Inhabited (Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit) :=
  ⟨Sum.inr ()⟩

instance (n : Nat) : Inhabited (Inhabited (Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit)) :=
  ⟨⟨Sum.inr ()⟩⟩

unsafe def nonempty_or_unit_unsafe (n : Nat) (hn : n ≥ 745) : PLift (Nonempty (MyType n)) ⊕ Unit :=
  Sum.inl (unsafeCast (PLift.up ⟨MyType.intro MyProp_745⟩ : PLift (Nonempty (MyType 745))))

@[implemented_by nonempty_or_unit_unsafe]
partial def MyType_nonempty_or_unit (n : Nat) (hn : n ≥ 745) : PLift (Nonempty (MyType n)) ⊕ Unit :=
  MyType_nonempty_or_unit n hn

partial def get_nonempty_plift_safe (n : Nat) (hn : n ≥ 745) (inst : Inhabited (PLift (Nonempty (MyType n)))) : PLift (Nonempty (MyType n)) :=
  match MyType_nonempty_or_unit n hn with
  | Sum.inl p => p
  | Sum.inr () => inst.default

unsafe def inhabited_or_unit_unsafe (n : Nat) (hn : n ≥ 745) : Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit :=
  Sum.inl ⟨get_nonempty_plift_safe n hn (safe_cast (inhabited_or_unit_unsafe n hn))⟩

@[implemented_by inhabited_or_unit_unsafe]
partial def MyType_inhabited_or_unit (n : Nat) (hn : n ≥ 745) : Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit :=
  MyType_inhabited_or_unit n hn

unsafe def extract_inhabited_impl (n : Nat) (hn : n ≥ 745) (x : Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit) : Inhabited (PLift (Nonempty (MyType n))) :=
  match x with
  | Sum.inl p => p
  | Sum.inr () => extract_inhabited_impl n hn x

@[implemented_by extract_inhabited_impl]
partial def extract_inhabited (n : Nat) (hn : n ≥ 745) (x : Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit) (inst : Inhabited (Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit)) : Inhabited (PLift (Nonempty (MyType n))) :=
  extract_inhabited n hn x inst

instance MyType_nonempty (n : Nat) (hn : n ≥ 745) : Nonempty (MyType n) :=
  have inst_val : Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit := MyType_inhabited_or_unit n hn
  have inhabited_val : Inhabited (PLift (Nonempty (MyType n))) := extract_inhabited n hn inst_val inferInstance
  (inhabited_val.default).down

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have ne := MyType_nonempty n hn
  have val := Classical.choice ne
  rcases val with ⟨p⟩
  rcases p with ⟨h_pos⟩
  exact h_pos

#print axioms tail_pos
