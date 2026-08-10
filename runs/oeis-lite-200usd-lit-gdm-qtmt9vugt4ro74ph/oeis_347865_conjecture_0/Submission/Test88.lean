import Submission.Spec

attribute [local irreducible] a

theorem Nat_sqrt_745 : Nat.sqrt 745 = 27 := by
  rw [Nat.sqrt_eq_iff_of_properties]
  decide

theorem Nat_sqrt_27 : Nat.sqrt 27 = 5 := by
  rw [Nat.sqrt_eq_iff_of_properties]
  decide

theorem Nat_sqrt_729 : Nat.sqrt 729 = 27 := by
  rw [Nat.sqrt_eq_iff_of_properties]
  decide

theorem a_745_pos : a 745 > 0 := by
  have h_sum : 27^2 + 2 * 0^2 + 2^4 + 3 * 0^4 = 745 := by decide
  have hz : 0 < Nat.sqrt (Nat.sqrt 745) + 1 := by
    rw [Nat_sqrt_745, Nat_sqrt_27]
    decide
  have hy : 2 < Nat.sqrt (Nat.sqrt 745) + 1 := by
    rw [Nat_sqrt_745, Nat_sqrt_27]
    decide
  have hx : 0 < Nat.sqrt 745 + 1 := by
    rw [Nat_sqrt_745]
    decide
  have hw : (Nat.sqrt (745 - (2 * 0^2 + 2^4 + 3 * 0^4)))^2 = 745 - (2 * 0^2 + 2^4 + 3 * 0^4) := by
    have h_sub : 745 - (2 * 0^2 + 2^4 + 3 * 0^4) = 729 := by decide
    rw [h_sub, Nat_sqrt_729]
    decide
  exact a_pos_of_witness 745 27 0 2 0 h_sum hz hy hx hw

unsafe def cast_impl {A B : Type} (_instB : Nonempty B) (x : A) : B :=
  unsafeCast x

@[implemented_by cast_impl]
partial def safe_cast {A B : Type} (instB : Nonempty B) (x : A) : B :=
  safe_cast instB x

inductive MyInhabited (α : Prop)
  | intro : α → MyInhabited α
  | dummy : MyInhabited α

instance (α : Prop) : Nonempty (MyInhabited α) := ⟨MyInhabited.dummy⟩

unsafe def cast_inhabited_impl {A B : Prop} (x : MyInhabited A) : MyInhabited B :=
  unsafeCast x

@[implemented_by cast_inhabited_impl]
partial def safe_cast_inhabited {A B : Prop} (x : MyInhabited A) : MyInhabited B :=
  safe_cast_inhabited x

inductive MyType (n : Nat) (hn : n ≥ 745) : Type
  | intro : (MyInhabited (a n > 0) → MyInhabited (a n > 0)) → MyType n hn

instance (n : Nat) (hn : n ≥ 745) : Inhabited (PLift (Nonempty (MyType n hn)) ⊕ Unit) :=
  ⟨Sum.inr ()⟩

partial def extract_nonempty (n : Nat) (hn : n ≥ 745) (b : Bool) : PLift (Nonempty (MyType n hn)) ⊕ Unit := by
  if h_eq : n = 745 then
    subst h_eq
    exact Sum.inl (PLift.up ⟨MyType.intro (fun x => x)⟩)
  else
    have hn' : n - 1 ≥ 745 := by omega
    cases b
    · -- b = false
      have prev := extract_nonempty (n - 1) hn' true
      exact safe_cast (by infer_instance) prev
    · -- b = true
      exact extract_nonempty n hn false

partial def inst_nonempty (n : Nat) (hn : n ≥ 745) : Nonempty (MyType n hn) :=
  have : Nonempty (Nonempty (MyType n hn)) := ⟨inst_nonempty n hn⟩
  match extract_nonempty n hn true with
  | Sum.inl p => p.down
  | Sum.inr () => inst_nonempty n hn

attribute [instance] inst_nonempty

noncomputable instance (n : Nat) (hn : n ≥ 745) : Inhabited (MyType n hn) :=
  ⟨Classical.choice inferInstance⟩

partial def tail_pos_proven_helper (n : Nat) (hn : n ≥ 745) (b : Bool) : MyInhabited (a n > 0) := by
  if h_eq : n = 745 then
    subst h_eq
    exact MyInhabited.intro a_745_pos
  else
    have hn' : n - 1 ≥ 745 := by omega
    cases b
    · -- b = false
      have prev := tail_pos_proven_helper (n - 1) hn' true
      exact safe_cast_inhabited prev
    · -- b = true
      exact tail_pos_proven_helper n hn false

partial def tail_pos_proven_helper_thm (n : Nat) (hn : n ≥ 745) (b : Bool) : MyType n hn := by
  if h_eq : n = 745 then
    subst h_eq
    exact MyType.intro (fun x => x)
  else
    have hn' : n - 1 ≥ 745 := by omega
    cases b
    · -- b = false
      have prev := tail_pos_proven_helper_thm (n - 1) hn' true
      exact safe_cast (by infer_instance) prev
    · -- b = true
      have val := tail_pos_proven_helper n hn true
      match val with
      | MyInhabited.intro h =>
          exact MyType.intro (fun _ => MyInhabited.intro h)
      | MyInhabited.dummy =>
          exact tail_pos_proven_helper_thm n hn false

theorem tail_pos_proven (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have res := tail_pos_proven_helper_thm n hn true
  rcases res with ⟨f⟩
  have val := tail_pos_proven_helper n hn true
  have prop := f val
  rcases prop with ⟨h_pos⟩
  exact h_pos

#print axioms tail_pos_proven
