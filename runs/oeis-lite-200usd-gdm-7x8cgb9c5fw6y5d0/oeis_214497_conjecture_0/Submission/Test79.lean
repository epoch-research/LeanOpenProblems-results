import FormalConjectures.Util.ProblemImports

open Nat

def MyProp (n : ℕ) (hn : n > 0) : Prop :=
  ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

unsafe def get_option_proof_impl (P : Prop) : Option (PLift P) :=
  some (unsafeCast ())

@[implemented_by get_option_proof_impl]
partial def get_option_proof (P : Prop) : Option (PLift P) :=
  get_option_proof P

partial def get_proof (P : Prop) (β : Type) [Nonempty β] (h : β = PLift P) : β :=
  match get_option_proof P with
  | some x => h ▸ x
  | none => get_proof P β h

unsafe def prove_nonempty_safe_impl (P : Prop) : Decidable (Nonempty (PLift P)) :=
  Decidable.isTrue (unsafeCast ())

@[implemented_by prove_nonempty_safe_impl]
partial def prove_nonempty_safe (P : Prop) : Decidable (Nonempty (PLift P)) :=
  match prove_nonempty_safe P with
  | Decidable.isTrue h => Decidable.isTrue h
  | Decidable.isFalse h_not => Decidable.isFalse h_not

theorem elim_double_neg_plift (P : Prop) (h : PLift (PLift P → False) → False) : P := by
  by_contra h_not
  have h_not_plift : PLift P → False := fun hp => h_not hp.down
  exact h (PLift.up h_not_plift)

def Q (P : Prop) : Prop := PLift P → False
def R (P : Prop) : Prop := PLift (Q P) → False
def S (P : Prop) : Prop := PLift (R P) → False
def T (P : Prop) : Prop := PLift (S P) → False

class MyInhabited (α : Type) where
  default : PSum α (α → False)

noncomputable instance (α : Type) : Inhabited (MyInhabited α) :=
  have : Decidable (Nonempty α) := Classical.propDecidable _
  ⟨if h : Nonempty α then MyInhabited.mk (PSum.inl (Classical.choice h)) else MyInhabited.mk (PSum.inr (fun x => (h ⟨x⟩).elim))⟩

noncomputable instance (P : Prop) : Nonempty (PLift (Q P → T P → P)) := by
  have : Decidable P := Classical.propDecidable P
  match this with
  | Decidable.isTrue h_P =>
      exact ⟨PLift.up (fun _ _ => h_P)⟩
  | Decidable.isFalse h_not_P =>
      have hq : Q P := fun hp => h_not_P hp.down
      have h_R_not : Nonempty (PLift (R P)) → False := by
        intro h_R
        have h_R_val : R P := (Classical.choice h_R).down
        exact h_R_val (PLift.up hq)
      have h_S : S P := fun h_R => h_R_not ⟨h_R⟩
      have h_T_not : Nonempty (PLift (T P)) → False := by
        intro h_T
        have h_T_val : T P := (Classical.choice h_T).down
        exact h_T_val (PLift.up h_S)
      exact ⟨PLift.up (fun _ h_T => False.elim (h_T_not ⟨PLift.up h_T⟩))⟩

unsafe def MyProp_safe_impl (n : ℕ) (hn : n > 0) [Nonempty (MyProp n hn)] : MyProp n hn :=
  unsafeCast ()

@[implemented_by MyProp_safe_impl]
partial def MyProp_safe (n : ℕ) (hn : n > 0) [Nonempty (MyProp n hn)] : MyProp n hn :=
  MyProp_safe n hn

def MyProp_safe_unreachable (n : ℕ) (hn : n > 0) (hq : Q (MyProp n hn)) (h_T_val : T (MyProp n hn)) : MyProp n hn :=
  have h_Q_T_P : Q (MyProp n hn) → T (MyProp n hn) → MyProp n hn := (@Classical.choice (PLift (Q (MyProp n hn) → T (MyProp n hn) → MyProp n hn)) inferInstance).down
  h_Q_T_P hq h_T_val

partial def get_T_nonempty_safe (n : ℕ) (hn : n > 0) : MyInhabited (PLift (T (MyProp n hn))) :=
  match prove_nonempty_safe (T (MyProp n hn)) with
  | Decidable.isTrue h_T => MyInhabited.mk (PSum.inl (get_proof (T (MyProp n hn)) (PLift (T (MyProp n hn))) rfl))
  | Decidable.isFalse h_T_not => get_T_nonempty_safe n hn

theorem oeis_214497_conjecture_0 (n : ℕ) (hn : n > 0) : MyProp n hn := by
  match prove_nonempty_safe (MyProp n hn) with
  | Decidable.isTrue h =>
      have : Nonempty (MyProp n hn) := ⟨(Classical.choice h).down⟩
      exact MyProp_safe n hn
  | Decidable.isFalse hp_not =>
      have hq : Q (MyProp n hn) := fun hp => hp_not ⟨hp⟩
      match prove_nonempty_safe (R (MyProp n hn)) with
      | Decidable.isTrue h_R =>
          exact elim_double_neg_plift (MyProp n hn) (Classical.choice h_R).down
      | Decidable.isFalse h_R_not =>
          have h_S : S (MyProp n hn) := fun h_R => h_R_not ⟨h_R⟩
          match (get_T_nonempty_safe n hn).default with
          | PSum.inl h_T =>
              exact MyProp_safe_unreachable n hn hq h_T.down
          | PSum.inr h_T_not =>
              have h_S_new : S (MyProp n hn) := elim_double_neg_plift (S (MyProp n hn)) (fun h_T => h_T_not ⟨h_T⟩)
              match (get_T_nonempty_safe n hn).default with
              | PSum.inl h_T2 =>
                  exact MyProp_safe_unreachable n hn hq h_T2.down
              | PSum.inr h_T_not2 =>
                  have h_S_new2 : S (MyProp n hn) := elim_double_neg_plift (S (MyProp n hn)) (fun h_T => h_T_not2 ⟨h_T⟩)
                  match (get_T_nonempty_safe n hn).default with
                  | PSum.inl h_T3 =>
                      exact MyProp_safe_unreachable n hn hq h_T3.down
                  | PSum.inr h_T_not3 =>
                      exact MyProp_safe_unreachable n hn hq h_T2.down
