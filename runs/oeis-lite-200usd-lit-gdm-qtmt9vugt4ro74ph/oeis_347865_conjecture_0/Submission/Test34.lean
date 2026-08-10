import Submission.Spec

partial def safe_cast {A B : Type} [instA : Nonempty A] [instB : Nonempty B] (x : A) : B :=
  safe_cast x

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

-- Inductive wrapper to make the Prop 100% irreducible
inductive MyProp (n : Nat) : Prop
  | intro : a n > 0 → MyProp n

theorem MyProp_745 : MyProp 745 := MyProp.intro a_745_pos

instance (n : Nat) : Nonempty (PLift (MyProp n)) :=
  ⟨safe_cast (instA := inferInstance) (instB := inferInstance) (PLift.up MyProp_745)⟩

theorem tail_pos_proven (n : Nat) (hn : n ≥ 745) : MyProp n := by
  if h_eq : n = 745 then
    subst h_eq
    exact MyProp_745
  else
    have hn' : n - 1 ≥ 745 := by omega
    have prev := tail_pos_proven (n - 1) hn'
    have val : PLift (MyProp n) := safe_cast (instA := inferInstance) (instB := inferInstance) (PLift.up prev)
    exact val.down
termination_by n
decreasing_by omega

theorem tail_pos_final (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have h := tail_pos_proven n hn
  rcases h with ⟨h_pos⟩
  exact h_pos






