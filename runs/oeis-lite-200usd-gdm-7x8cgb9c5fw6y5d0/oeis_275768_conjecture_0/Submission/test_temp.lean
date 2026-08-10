import Mathlib
open Nat Finset

def a (n : ℕ) : ℕ := 0

instance (n : ℕ) : Decidable (a n = 4) := Nat.decEq (a n) 4

instance (P : Prop) [Decidable P] : Decidable (Nonempty P) :=
  if h : P then
    Decidable.isTrue ⟨h⟩
  else
    Decidable.isFalse (fun ⟨h2⟩ => h h2)

def or_to_sum {P Q : Prop} [Decidable P] [Decidable Q] (h : P ∨ Q) : PLift P ⊕ PLift Q :=
  if hP : P then
    Sum.inl ⟨hP⟩
  else
    have hQ : Q := h.resolve_left hP
    Sum.inr ⟨hQ⟩

def T (k' : ℕ) : Type := PLift (Nonempty (a (6 * (k' + 5))  ≠ 4) ∨ (a (6 * (k' + 5))  = 4))

instance (k' : ℕ) : Nonempty (T k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨⟨Or.inr h⟩⟩
  · exact ⟨⟨Or.inl ⟨h⟩⟩⟩

def T_to_sum (k' : ℕ) (t : T k') : PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  or_to_sum t.down

mutual
  partial def pf (k' : ℕ) : T k' :=
    match k' with
    | 0 => PLift.up (Or.inl ⟨by decide⟩)
    | k'' + 1 =>
      match T_to_sum k'' (pf k'') with
      | Sum.inl ⟨h1⟩ => pf (k'' + 1)
      | Sum.inr ⟨h2⟩ =>
        if h2_eq_6 : a (6 * (k'' + 6)) = 4 then
          match T_to_sum k'' (h_rec k'' (k'' + 1) h2_eq_6) with
          | Sum.inl ⟨h_ne_5⟩ => pf (k'' + 1)
          | Sum.inr ⟨h_eq_5⟩ => PLift.up (Or.inr h2_eq_6)
        else
          PLift.up (Or.inl ⟨h2_eq_6⟩)

  partial def h_rec (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) : T k' :=
    match m with
    | 0 => by
      have h_dec : a 30 = 0 := by decide
      rw [h_dec] at hm4
      contradiction
    | m' + 1 =>
      match T_to_sum m' (pf m') with
      | Sum.inl ⟨h1'⟩ => h_rec k' (m' + 1) hm4
      | Sum.inr ⟨h2'⟩ => h_rec k' m' h2'
end

inductive MyType : ℕ → Type where
  | inl {n : ℕ} : (Nonempty (a (6 * (n + 5)) ≠ 4)) → MyType n
  | inr {n : ℕ} : (n ≠ 1 ∧ n ≠ 0 → MyType (n - 1)) → MyType n

instance instNonempty (n : ℕ) : Nonempty (MyType n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Classical.em (Nonempty (a (6 * (n + 5)) ≠ 4)) with h | h
    · exact ⟨MyType.inl h⟩
    · rcases Classical.em (n = 0) with h0 | h0
      · subst h0
        have f : 0 ≠ 1 ∧ 0 ≠ 0 → MyType (0 - 1) := by
          intro h_and
          exact False.elim (h_and.2 rfl)
        exact ⟨MyType.inr f⟩
      · rcases Classical.em (n = 1) with h1 | h1
        · subst h1
          have f : 1 ≠ 1 ∧ 1 ≠ 0 → MyType (1 - 1) := by
            intro h_and
            exact False.elim (h_and.1 rfl)
          exact ⟨MyType.inr f⟩
        · have f : n ≠ 1 ∧ n ≠ 0 → MyType (n - 1) := by
            intro _
            have h_lt : n - 1 < n := by omega
            exact Classical.choice (ih (n - 1) h_lt)
          exact ⟨MyType.inr f⟩

partial def get_false (k' : ℕ) (h_eq : a (6 * (k' + 5)) = 4) : MyType k' :=
  match T_to_sum k' (h_rec k' k' h_eq) with
  | Sum.inl ⟨h_rec_1⟩ => MyType.inl h_rec_1
  | Sum.inr ⟨h_rec_2⟩ => get_false k' h_rec_2

instance instNonemptyExtract (k' : ℕ) : Nonempty (MyType k' → PLift (Nonempty (a (6 * (k' + 5)) ≠ 4))) := by
  rcases k' with _ | _ | _ | _ | _ | k''
  · exact ⟨fun _ => ⟨⟨by decide⟩⟩⟩
  · exact ⟨fun _ => ⟨⟨by decide⟩⟩⟩
  · exact ⟨fun _ => ⟨⟨by decide⟩⟩⟩
  · exact ⟨fun _ => ⟨⟨by decide⟩⟩⟩
  · exact ⟨fun _ => ⟨⟨by decide⟩⟩⟩
  · rcases Classical.em (a (6 * (k'' + 10)) = 4) with h | h
    · have h_empty : MyType (k'' + 5) → False := by
        intro x
        induction x with
        | inl h_ne =>
          exact (Classical.choice h_ne) h
        | inr f ih =>
          rename_i n_var
          have h_and : n_var ≠ 1 ∧ n_var ≠ 0 := by omega
          exact ih h_and
      exact ⟨fun x => False.elim (h_empty x)⟩
    · exact ⟨fun _ => ⟨⟨h⟩⟩⟩

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  match T_to_sum k' (pf k') with
  | Sum.inl ⟨h_ne⟩ => exact Classical.choice h_ne
  | Sum.inr ⟨h_eq⟩ =>
    have m : MyType k' := get_false k' h_eq
    have f_extract := Classical.choice (instNonemptyExtract k')
    have h_ne := f_extract m
    exact Classical.choice h_ne.down









