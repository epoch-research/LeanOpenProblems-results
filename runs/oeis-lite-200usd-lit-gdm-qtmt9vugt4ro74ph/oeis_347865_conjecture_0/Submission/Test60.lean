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

instance (n : Nat) : Inhabited (Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit) :=
  ⟨Sum.inr ()⟩

instance (n : Nat) : Inhabited (Inhabited (Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit)) :=
  ⟨⟨Sum.inr ()⟩⟩

noncomputable def get_inhabited_inst_safe (n : Nat) (hn : n ≥ 745) : Inhabited (Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit) :=
  if h_eq : n = 745 then
    ⟨Sum.inl ⟨PLift.up ⟨MyType.intro MyProp_745⟩⟩⟩
  else
    have hn' : n - 1 ≥ 745 := by omega
    have ih := get_inhabited_inst_safe (n - 1) hn'
    safe_cast ih
termination_by n
decreasing_by omega

unsafe def extract_impl (n : Nat) (hn : n ≥ 745) (x : Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit) (inst : Inhabited (Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit)) : Inhabited (PLift (Nonempty (MyType n))) :=
  match x with
  | Sum.inl p => p
  | Sum.inr () => extract_impl n hn x inst

@[implemented_by extract_impl]
partial def extract (n : Nat) (hn : n ≥ 745) (x : Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit) (inst : Inhabited (Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit)) : Inhabited (PLift (Nonempty (MyType n))) :=
  @safe_cast _ _ (safe_cast inst) x

instance MyType_nonempty (n : Nat) (hn : n ≥ 745) : Nonempty (MyType n) :=
  have inst_val : Inhabited (Inhabited (PLift (Nonempty (MyType n))) ⊕ Unit) := get_inhabited_inst_safe n hn
  have inhabited_val : Inhabited (PLift (Nonempty (MyType n))) := extract n hn inst_val.default inferInstance
  (inhabited_val.default).down

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have ne := MyType_nonempty n hn
  have val := Classical.choice ne
  rcases val with ⟨p⟩
  rcases p with ⟨h_pos⟩
  exact h_pos

#print axioms tail_pos
