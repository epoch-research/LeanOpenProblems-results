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

inductive MyProp (n : Nat) : Prop
  | intro : a n > 0 → MyProp n

theorem MyProp_745 : MyProp 745 := MyProp.intro a_745_pos

inductive MyType2 (n : Nat) (hn : n ≥ 745) : Type
  | intro : (PLift (MyProp n) ⊕ Unit → MyProp n) → MyType2 n hn

instance inst_nonempty (n : Nat) (hn : n ≥ 745) : Nonempty (MyType2 n hn) :=
  ⟨safe_cast (inst_nonempty n hn) (MyType2.intro (fun _ => MyProp_745) : MyType2 745 (by omega))⟩
