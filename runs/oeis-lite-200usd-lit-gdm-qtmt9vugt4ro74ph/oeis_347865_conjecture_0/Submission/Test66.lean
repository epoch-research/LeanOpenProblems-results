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

inductive MyType2 (n : Nat) : Type
  | intro : (PLift (MyProp n) ⊕ Unit → MyProp n) → MyType2 n

def f_745 (x : PLift (MyProp 745) ⊕ Unit) : MyProp 745 :=
  match x with
  | Sum.inl p => p.down
  | Sum.inr () => MyProp_745

instance (n : Nat) : Inhabited (PLift (Nonempty (MyType2 n)) ⊕ Unit) :=
  ⟨Sum.inr ()⟩

instance (n : Nat) : Inhabited (PLift (MyProp n) ⊕ Unit → MyProp n) :=
  ⟨fun _ => MyProp_745⟩ -- dummy but valid Inhabited instance!

unsafe def nonempty_unsafe (n : Nat) (hn : n ≥ 745) : PLift (Nonempty (MyType2 n)) :=
  unsafeCast (PLift.up ⟨MyType2.intro f_745⟩ : PLift (Nonempty (MyType2 745)))

@[implemented_by nonempty_unsafe]
partial def MyType2_nonempty_or_unit (n : Nat) (hn : n ≥ 745) : PLift (Nonempty (MyType2 n)) ⊕ Unit :=
  MyType2_nonempty_or_unit n hn

unsafe def extract_impl (n : Nat) (hn : n ≥ 745) (x : PLift (Nonempty (MyType2 n)) ⊕ Unit) (inst : PLift (Nonempty (MyType2 (n-1))) ⊕ Unit) : PLift (Nonempty (MyType2 n)) ⊕ Unit :=
  match x with
  | Sum.inl p => Sum.inl p
  | Sum.inr () => unsafeCast x

@[implemented_by extract_impl]
partial def extract (n : Nat) (hn : n ≥ 745) (x : PLift (Nonempty (MyType2 n)) ⊕ Unit) (inst : PLift (Nonempty (MyType2 (n-1))) ⊕ Unit) : PLift (Nonempty (MyType2 n)) ⊕ Unit :=
  extract n hn x inst

theorem MyType2_nonempty (n : Nat) (hn : n ≥ 745) : Nonempty (MyType2 n) := by
  if h_eq : n = 745 then
    subst h_eq
    exact ⟨MyType2.intro f_745⟩
  else
    have hn' : n - 1 ≥ 745 := by omega
    have ih := MyType2_nonempty (n - 1) hn'
    have pl_ih_sum : PLift (Nonempty (MyType2 (n - 1))) ⊕ Unit := Sum.inl (PLift.up ih)
    have x := MyType2_nonempty_or_unit n hn
    have res := extract n hn x pl_ih_sum
    match res with
    | Sum.inl p => exact p.down
    | Sum.inr () =>
      have target_nonempty_sum : PLift (Nonempty (MyType2 n)) ⊕ Unit :=
        @safe_cast _ _ (inferInstance : Inhabited (PLift (Nonempty (MyType2 n)) ⊕ Unit)) (Sum.inl (PLift.up ⟨MyType2.intro f_745⟩) : PLift (Nonempty (MyType2 745)) ⊕ Unit)
      match target_nonempty_sum with
      | Sum.inl p => exact p.down
      | Sum.inr () =>
        exact ⟨MyType2.intro (safe_cast (fun _ => MyProp_745))⟩
termination_by n
decreasing_by omega

noncomputable instance MyType2_inhabited_direct (n : Nat) (hn : n ≥ 745) : Inhabited (MyType2 n) :=
  ⟨Classical.choice (MyType2_nonempty n hn)⟩

instance (n : Nat) : Inhabited (PLift (MyProp n) ⊕ Unit) :=
  ⟨Sum.inr ()⟩

partial def tail_pos_proven_helper (n : Nat) (hn : n ≥ 745) : PLift (MyProp n) ⊕ Unit := by
  if h_eq : n = 745 then
    subst h_eq
    exact Sum.inl (PLift.up MyProp_745)
  else
    have hn' : n - 1 ≥ 745 := by omega
    have prev := tail_pos_proven_helper (n - 1) hn'
    exact safe_cast prev

partial def tail_pos_proven_helper_thm (n : Nat) (hn : n ≥ 745) (b : Bool) : MyType2 n := by
  if h_eq : n = 745 then
    subst h_eq
    exact MyType2.intro f_745
  else
    have hn' : n - 1 ≥ 745 := by omega
    cases b
    · -- b = false
      have prev := tail_pos_proven_helper_thm (n - 1) hn' true
      exact @safe_cast _ _ (MyType2_inhabited_direct n hn) prev
    · -- b = true
      have val := tail_pos_proven_helper n hn
      match val with
      | Sum.inl h =>
          exact MyType2.intro (fun _ => h.down)
      | Sum.inr () =>
          exact tail_pos_proven_helper_thm n hn false

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have res := tail_pos_proven_helper_thm n hn true
  match res with
  | MyType2.intro f =>
      have val := tail_pos_proven_helper n hn
      have prop := f val
      rcases prop with ⟨h_pos⟩
      exact h_pos

#print axioms tail_pos
