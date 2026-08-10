import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

inductive MyProp (k' : ℕ) : Prop where
  | intro : (a (6 * (k' + 5)) ≠ 4) → MyProp k'

def T (k' : ℕ) : Type := PLift (MyProp k' ∨ (a (6 * (k' + 5)) = 4))

def HRecType (k' : ℕ) (m : ℕ) : Type :=
  PLift (MyProp m ∨ (a (6 * (m + 5)) = 4 ∧ (MyProp k' ∨ a (6 * (k' + 5)) = 4)))

instance (k' : ℕ) : Nonempty (T k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨⟨Or.inr h⟩⟩
  · exact ⟨⟨Or.inl (MyProp.intro h)⟩⟩

instance (k' m : ℕ) : Nonempty (HRecType k' m) := by
  rcases Classical.em (a (6 * (m + 5)) = 4) with h | h
  · rcases Classical.em (a (6 * (k' + 5)) = 4) with h2 | h2
    · exact ⟨⟨Or.inr ⟨h, Or.inr h2⟩⟩⟩
    · exact ⟨⟨Or.inr ⟨h, Or.inl (MyProp.intro h2)⟩⟩⟩
  · exact ⟨⟨Or.inl (MyProp.intro h)⟩⟩

instance (P : Prop) [Decidable P] : Decidable (MyProp k') :=
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · apply Decidable.isFalse
    intro ⟨h_ne⟩
    exact h_ne h
  · apply Decidable.isTrue
    exact MyProp.intro h

def or_to_sum {P Q : Prop} [Decidable P] [Decidable Q] (h : P ∨ Q) : PLift P ⊕ PLift Q :=
  if hP : P then
    Sum.inl ⟨hP⟩
  else
    have hQ : Q := h.resolve_left hP
    Sum.inr ⟨hQ⟩

def T_to_sum (k' : ℕ) (t : T k') : PLift (MyProp k') ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  or_to_sum t.down

def HRec_to_sum (k' : ℕ) (m : ℕ) (t : HRecType k' m) :
    PLift (MyProp m) ⊕ PLift (a (6 * (m + 5)) = 4 ∧ (MyProp k' ∨ a (6 * (k' + 5)) = 4)) :=
  or_to_sum t.down

def sub_to_sum (k' : ℕ) (h : MyProp k' ∨ a (6 * (k' + 5)) = 4) :
    PLift (MyProp k') ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  or_to_sum h

mutual
  partial def pf (k' : ℕ) : T k' :=
    match k' with
    | 0 => PLift.up (Or.inl (MyProp.intro (by decide)))
    | k' + 1 =>
      match T_to_sum k' (pf k') with
      | Sum.inl ⟨h1⟩ => pf (k' + 1)
      | Sum.inr ⟨h2⟩ =>
        match HRec_to_sum k' k' (h_rec k' k' h2) with
        | Sum.inl ⟨MyProp.intro h_rec_1⟩ => False.elim (h_rec_1 h2)
        | Sum.inr ⟨_, h_rec_2⟩ => pf (k' + 1)

  partial def h_rec (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) : HRecType k' m :=
    match m with
    | 0 => by
      have h_dec : a 30 = 5 := by decide
      rw [h_dec] at hm4
      contradiction
    | m' + 1 =>
      match T_to_sum m' (pf m') with
      | Sum.inl ⟨h1'⟩ => h_rec k' (m' + 1) hm4
      | Sum.inr ⟨h2'⟩ =>
        match HRec_to_sum k' m' (h_rec k' m' h2') with
        | Sum.inl ⟨MyProp.intro h_res_1⟩ => False.elim (h_res_1 h2')
        | Sum.inr ⟨_, h_res_2⟩ =>
          match sub_to_sum k' h_res_2 with
          | Sum.inl ⟨MyProp.intro h_ne_k'⟩ =>
            if h_dec : m' = k' then
              have h_eq2' : a (6 * (k' + 5)) = 4 := by
                subst h_dec
                exact h2'
              False.elim (h_ne_k' h_eq2')
            else
              PLift.up (Or.inr ⟨hm4, Or.inl (MyProp.intro h_ne_k')⟩)
          | Sum.inr ⟨h_eq_k'⟩ =>
            PLift.up (Or.inr ⟨hm4, Or.inr h_eq_k'⟩)
end

partial def extract_false (k' : ℕ) (ih : a (6 * (k' + 5)) ≠ 4) (h_eq : a (6 * (k' + 6)) = 4) :
    T (k' + 1) :=
  match HRec_to_sum k' (k' + 1) (h_rec k' (k' + 1) h_eq) with
  | Sum.inl ⟨h_res_1⟩ => PLift.up (Or.inl h_res_1)
  | Sum.inr ⟨_, h_res_2⟩ =>
    match sub_to_sum k' h_res_2 with
    | Sum.inl ⟨MyProp.intro h_ne_5⟩ => extract_false k' h_ne_5 h_eq
    | Sum.inr ⟨h_eq_5⟩ =>
      have h_false : False := ih h_eq_5
      False.elim h_false

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  induction k' with
  | zero => decide
  | succ k'' ih =>
    have x := pf (k'' + 1)
    match x.down with
    | Or.inl (MyProp.intro h) => exact h
    | Or.inr h_eq =>
      have y := extract_false k'' ih h_eq
      exact match y.down with
      | Or.inl (MyProp.intro h) => h
