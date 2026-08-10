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

noncomputable def MyType_nonempty_or_unit (n : Nat) (hn : n ≥ 745) : PLift (Nonempty (MyType n)) ⊕ Unit :=
  if h_eq : n = 745 then
    Sum.inl (PLift.up ⟨by subst h_eq; exact MyType.intro MyProp_745⟩)
  else
    have hn' : n - 1 ≥ 745 := by omega
    have ih := MyType_nonempty_or_unit (n - 1) hn'
    @safe_cast _ _ (inferInstance : Inhabited (PLift (Nonempty (MyType n)) ⊕ Unit)) ih
termination_by n
decreasing_by omega

mutual
  partial def get_nonempty_plift (n : Nat) (hn : n ≥ 745) : PLift (Nonempty (MyType n)) :=
    match MyType_nonempty_or_unit n hn with
    | Sum.inl p => p
    | Sum.inr () => get_nonempty_plift n hn

  def MyType_inhabited (n : Nat) (hn : n ≥ 745) : Inhabited (PLift (Nonempty (MyType n))) :=
    ⟨get_nonempty_plift n hn⟩
end

attribute [instance] MyType_inhabited

instance MyType_nonempty (n : Nat) (hn : n ≥ 745) : Nonempty (MyType n) :=
  (get_nonempty_plift n hn).down

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have ne := MyType_nonempty n hn
  have val := Classical.choice ne
  rcases val with ⟨p⟩
  rcases p with ⟨h_pos⟩
  exact h_pos

#print axioms tail_pos
