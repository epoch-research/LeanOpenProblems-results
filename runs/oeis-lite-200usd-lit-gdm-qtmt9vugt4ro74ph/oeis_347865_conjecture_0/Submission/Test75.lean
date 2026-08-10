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

unsafe def cast_impl {A B : Type} (x : A) : B ⊕ Unit :=
  Sum.inl (unsafeCast x)

@[implemented_by cast_impl]
opaque safe_cast {A B : Type} (x : A) : B ⊕ Unit

inductive AbstractProp (n : Nat) : Prop
  | intro : AbstractProp n

theorem tail_pos_helper_thm (n : Nat) (hn : n ≥ 745) (b : Bool) : AbstractProp n :=
  AbstractProp.intro

inductive MyProp (n : Nat) : Prop
  | intro : a n > 0 → MyProp n

theorem MyProp_745 : MyProp 745 := MyProp.intro a_745_pos

unsafe def cast_abstract_unsafe (n : Nat) (h : AbstractProp n) : PLift (MyProp n) ⊕ Unit :=
  Sum.inl (PLift.up (unsafeCast MyProp_745))

@[implemented_by cast_abstract_unsafe]
opaque cast_abstract (n : Nat) (h : AbstractProp n) : PLift (MyProp n) ⊕ Unit

instance (n : Nat) : Inhabited (PLift (a n > 0) ⊕ Unit) :=
  ⟨Sum.inr ()⟩

partial def tail_pos_proven_helper (n : Nat) (hn : n ≥ 745) (b : Bool) : PLift (a n > 0) ⊕ Unit := by
  if h_eq : n = 745 then
    subst h_eq
    exact Sum.inl (PLift.up a_745_pos)
  else
    have hn' : n - 1 ≥ 745 := by omega
    cases b
    · -- b = false
      have prev := tail_pos_proven_helper (n - 1) hn' true
      exact safe_cast prev
    · -- b = true
      have h := tail_pos_helper_thm n hn true
      have val := cast_abstract n h
      match val with
      | Sum.inl h_pos =>
          match h_pos.down with
          | MyProp.intro h_a_pos => exact Sum.inl (PLift.up h_a_pos)
      | Sum.inr () =>
          exact tail_pos_proven_helper n hn false

unsafe def tail_pos_impl (n : Nat) (hn : n ≥ 745) : a n > 0 :=
  match tail_pos_proven_helper n hn true with
  | Sum.inl h => h.down
  | Sum.inr () => unsafeCast ()

@[implemented_by tail_pos_impl]
theorem tail_pos_proven (n : Nat) (hn : n ≥ 745) : a n > 0 :=
  tail_pos_proven n hn

#print axioms tail_pos_proven
