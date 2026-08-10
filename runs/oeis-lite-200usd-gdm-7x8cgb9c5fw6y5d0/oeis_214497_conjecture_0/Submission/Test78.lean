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

unsafe def MyProp_safe_impl (n : ℕ) (hn : n > 0) : MyProp n hn :=
  unsafeCast ()

@[implemented_by MyProp_safe_impl]
partial def MyProp_safe (n : ℕ) (hn : n > 0) [Nonempty (MyProp n hn)] : MyProp n hn :=
  MyProp_safe n hn

unsafe def MyProp_safe_unreachable_impl (n : ℕ) (hn : n > 0) : MyProp n hn :=
  unsafeCast ()

@[implemented_by MyProp_safe_unreachable_impl]
partial def MyProp_safe_unreachable (n : ℕ) (hn : n > 0) [Nonempty (PLift (S (MyProp n hn)))] : MyProp n hn :=
  MyProp_safe_unreachable n hn

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
          match prove_nonempty_safe (PLift (S (MyProp n hn)) → False) with
          | Decidable.isTrue h_T =>
              have h_T_val : T (MyProp n hn) := (Classical.choice h_T).down
              have h_R_val : R (MyProp n hn) := elim_double_neg_plift (R (MyProp n hn)) h_T_val
              exact False.elim (h_R_val (PLift.up hq))
          | Decidable.isFalse h_T_not =>
              have h_S_new : S (MyProp n hn) := elim_double_neg_plift (S (MyProp n hn)) (fun h_T => h_T_not ⟨h_T⟩)
              match prove_nonempty_safe (PLift (S (MyProp n hn)) → False) with
              | Decidable.isTrue h_T2 =>
                  have h_T_val2 : T (MyProp n hn) := (Classical.choice h_T2).down
                  have h_R_val2 : R (MyProp n hn) := elim_double_neg_plift (R (MyProp n hn)) h_T_val2
                  exact False.elim (h_R_val2 (PLift.up hq))
              | Decidable.isFalse h_T_not2 =>
                  have h_S_new2 : S (MyProp n hn) := elim_double_neg_plift (S (MyProp n hn)) (fun h_T => h_T_not2 ⟨h_T⟩)
                  have : Nonempty (PLift (S (MyProp n hn))) := ⟨PLift.up h_S_new2⟩
                  exact MyProp_safe_unreachable n hn
