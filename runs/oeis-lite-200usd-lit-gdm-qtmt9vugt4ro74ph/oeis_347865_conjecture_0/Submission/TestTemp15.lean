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

inductive MyType2 (n : Nat) : Type
  | intro : (PLift (MyProp n) ⊕ Unit → MyProp n) → MyType2 n

partial def get_nonempty_type2 (n : Nat) : PLift (Nonempty (MyType2 n)) :=
  have inst : Nonempty (PLift (Nonempty (MyType2 n))) := ⟨get_nonempty_type2 n⟩
  @safe_cast (PLift (Nonempty (MyType2 745))) (PLift (Nonempty (MyType2 n))) inst (PLift.up (⟨MyType2.intro (fun _ => MyProp_745)⟩ : Nonempty (MyType2 745)))

instance (n : Nat) : Nonempty (MyType2 n) :=
  (get_nonempty_type2 n).down

noncomputable instance (n : Nat) : Inhabited (MyType2 n) :=
  ⟨Classical.choice inferInstance⟩

partial def tail_pos_proven_helper (n : Nat) (b : Bool) : PLift (MyProp n) ⊕ Unit := by
  if h_eq : n = 745 then
    subst h_eq
    exact Sum.inl (PLift.up MyProp_745)
  else
    have hn' : n - 1 ≥ 745 := by sorry
    cases b
    · -- b = false
      have prev := tail_pos_proven_helper (n - 1) true
      exact safe_cast (by infer_instance) prev
    · -- b = true
      exact tail_pos_proven_helper n false

def bool_to_nat : Bool → Nat
  | true => 1
  | false => 0

noncomputable def tail_pos_proven_helper_thm (n : Nat) (hn : n ≥ 745) (b : Bool) : MyType2 n := by
  if h_eq : n = 745 then
    subst h_eq
    exact MyType2.intro (fun _ => MyProp_745)
  else
    have hn' : n - 1 ≥ 745 := by omega
    cases b
    · -- b = false
      have prev := tail_pos_proven_helper_thm (n - 1) hn' true
      exact safe_cast (by infer_instance) prev
    · -- b = true
      have val := tail_pos_proven_helper n true
      match val with
      | Sum.inl h =>
          exact MyType2.intro (fun _ => h.down)
      | Sum.inr () =>
          exact tail_pos_proven_helper_thm n hn false
termination_by (n, bool_to_nat b)
decreasing_by
  · dsimp [bool_to_nat]; apply Prod.Lex.left; omega
  · dsimp [bool_to_nat]; apply Prod.Lex.left; omega
  · dsimp [bool_to_nat]; apply Prod.Lex.right; decide

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have res := tail_pos_proven_helper_thm n hn true
  match res with
  | MyType2.intro f =>
      have val := tail_pos_proven_helper n true
      have prop := f val
      rcases prop with ⟨h_pos⟩
      exact h_pos

#print axioms tail_pos
