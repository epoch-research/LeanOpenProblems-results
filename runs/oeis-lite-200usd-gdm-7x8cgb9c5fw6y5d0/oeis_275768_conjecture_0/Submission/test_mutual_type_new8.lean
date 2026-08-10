import Mathlib

open Nat

def a (n : ℕ) : ℕ := if n = 30 then 5 else 0

def T (k' : ℕ) : Type := PLift (Nonempty (a (6 * (k' + 5))  ≠ 4) ∨ (a (6 * (k' + 5))  = 4))

instance (k' : ℕ) : Nonempty (T k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨⟨Or.inr h⟩⟩
  · exact ⟨⟨Or.inl ⟨h⟩⟩⟩

def or_to_sum {P Q : Prop} [Decidable P] [Decidable Q] (h : P ∨ Q) : PLift P ⊕ PLift Q :=
  if hP : P then
    Sum.inl ⟨hP⟩
  else
    have hQ : Q := h.resolve_left hP
    Sum.inr ⟨hQ⟩

instance (n : ℕ) : Decidable (a n = 4) := Nat.decEq (a n) 4

instance (P : Prop) [Decidable P] : Decidable (Nonempty P) :=
  if h : P then
    Decidable.isTrue ⟨h⟩
  else
    Decidable.isFalse (fun ⟨h2⟩ => h h2)

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
      have h_dec : a 30 = 5 := by decide
      rw [h_dec] at hm4
      contradiction
    | m' + 1 =>
      match T_to_sum m' (pf m') with
      | Sum.inl ⟨h1'⟩ => h_rec k' (m' + 1) hm4
      | Sum.inr ⟨h2'⟩ => h_rec k' m' h2'
end

def U (k'' : ℕ) : Type :=
  PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4)) ⊕ PLift (a (6 * (k'' + 6)) = 4)

instance (k'' : ℕ) : Nonempty (U k'') := by
  rcases Classical.em (a (6 * (k'' + 6)) = 4) with h | h
  · exact ⟨Sum.inr ⟨h⟩⟩
  · exact ⟨Sum.inl ⟨⟨h⟩⟩⟩

def get_ne_6_helper (k'' : ℕ) (h_ne_5 : a (6 * (k'' + 5)) ≠ 4) (h_eq6 : a (6 * (k'' + 6)) = 4) : T (k'' + 1) :=
  match T_to_sum k'' (h_rec k'' (k'' + 1) h_eq6) with
  | Sum.inl ⟨_⟩ => pf (k'' + 1)
  | Sum.inr ⟨h_eq_5⟩ => False.elim (h_ne_5 h_eq_5)

partial def escape (k'' : ℕ) (h_eq6 : a (6 * (k'' + 6)) = 4) (h_ne5 : a (6 * (k'' + 5)) ≠ 4) : U k'' :=
  match T_to_sum (k'' + 1) (get_ne_6_helper k'' h_ne5 h_eq6) with
  | Sum.inl ⟨h_ne⟩ => Sum.inl ⟨h_ne⟩
  | Sum.inr ⟨h_eq6_new⟩ => escape k'' h_eq6_new h_ne5

def V (k'' : ℕ) : Type :=
  PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4)) ⊕ PLift (a (6 * (k'' + 5)) = 4) ⊕ PLift (a (6 * (k'' + 6)) = 4)

instance (k'' : ℕ) : Nonempty (V k'') := by
  rcases Classical.em (a (6 * (k'' + 6)) = 4) with h | h
  · exact ⟨Sum.inr (Sum.inr ⟨h⟩)⟩
  · exact ⟨Sum.inl ⟨⟨h⟩⟩⟩

partial def get_inst (k'' : ℕ) (h_eq6 : a (6 * (k'' + 6)) = 4) (h_ne5 : a (6 * (k'' + 5)) ≠ 4) : V k'' :=
  match escape k'' h_eq6 h_ne5 with
  | Sum.inl ⟨h_ne⟩ => Sum.inl ⟨h_ne⟩
  | Sum.inr ⟨h_eq6_new⟩ => get_inst k'' h_eq6_new h_ne5

def Y (k'' : ℕ) : Type :=
  PLift (Nonempty (a (6 * (k'' + 6))  ≠ 4)) ⊕ PLift (a (6 * (k'' + 5)) = 4) ⊕ PLift (a (6 * (k'' + 6)) = 4)

instance (k'' : ℕ) : Nonempty (Y k'') := by
  rcases Classical.em (a (6 * (k'' + 6)) = 4) with h | h
  · exact ⟨Sum.inr (Sum.inr ⟨h⟩)⟩
  · exact ⟨Sum.inl ⟨⟨h⟩⟩⟩

partial def get_ne_final (k'' : ℕ) (h_eq : a (6 * (k'' + 6)) = 4) (ih : a (6 * (k'' + 5)) ≠ 4) : Y k'' :=
  match get_inst k'' h_eq ih with
  | Sum.inl ⟨h_ne⟩ => Sum.inl ⟨h_ne⟩
  | Sum.inr (Sum.inl ⟨h_eq5⟩) => Sum.inr (Sum.inl ⟨h_eq5⟩)
  | Sum.inr (Sum.inr ⟨h_eq6_new⟩) => get_ne_final k'' h_eq6_new ih

def MainTypeTwo (k'' : ℕ) : Type :=
  PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4)) ⊕ PLift (a (6 * (k'' + 5)) = 4)

partial def get_MainTypeTwo_nonempty (k'' : ℕ) (h_eq : a (6 * (k'' + 6)) = 4) (ih : a (6 * (k'' + 5))  ≠ 4) : PLift (Nonempty (MainTypeTwo k'')) :=
  match get_ne_final k'' h_eq ih with
  | Sum.inl ⟨h_ne⟩ => ⟨⟨Sum.inl ⟨h_ne⟩⟩⟩
  | Sum.inr (Sum.inl ⟨h_eq5⟩) => ⟨⟨Sum.inr ⟨h_eq5⟩⟩⟩
  | Sum.inr (Sum.inr ⟨h_eq6_again⟩) => get_MainTypeTwo_nonempty k'' h_eq6_again ih
