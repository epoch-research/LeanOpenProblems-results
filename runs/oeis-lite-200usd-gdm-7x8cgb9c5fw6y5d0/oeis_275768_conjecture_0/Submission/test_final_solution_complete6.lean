import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

inductive MyProp : ℕ → Type
  | intro : ∀ (k' : ℕ), (a (6 * (k' + 5))  ≠ 4) → MyProp k'
  | dummy : ∀ (k' : ℕ), (a (6 * (k' + 5))  = 4) → MyProp (k' - 1) → MyProp k'

instance (k' : ℕ) : Nonempty (MyProp k') := by
  induction k' with
  | zero =>
    have h_ne : a 30 ≠ 4 := by decide
    exact ⟨MyProp.intro 0 h_ne⟩
  | succ k'' ih =>
    rcases Classical.em (a (6 * (k'' + 6)) = 4) with h | h
    · exact ⟨MyProp.dummy (k'' + 1) h (Classical.choice ih)⟩
    · exact ⟨MyProp.intro (k'' + 1) h⟩

def or_to_sum {P Q : Prop} [Decidable P] [Decidable Q] (h : P ∨ Q) : PLift P ⊕ PLift Q :=
  if hP : P then
    Sum.inl ⟨hP⟩
  else
    have hQ : Q := h.resolve_left hP
    Sum.inr ⟨hQ⟩

instance (P : Prop) [Decidable P] : Decidable (Nonempty P) :=
  if h : P then
    Decidable.isTrue ⟨h⟩
  else
    Decidable.isFalse (fun ⟨h2⟩ => h h2)

def T (k' : ℕ) : Type := PLift (Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ a (6 * (k' + 5)) = 4)

instance (k' : ℕ) : Nonempty (T k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨⟨Or.inr h⟩⟩
  · exact ⟨⟨Or.inl ⟨h⟩⟩⟩

def T_to_sum (k' : ℕ) (t : T k') : PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  or_to_sum t.down

partial def pf (k' : ℕ) : T k' := pf k'

partial def extract_inl (k' : ℕ) (m : MyProp k') : T k' :=
  match m with
  | MyProp.intro _ h_ne => PLift.up (Or.inl ⟨h_ne⟩)
  | MyProp.dummy _ _ m_prev =>
    match k' with
    | 0 => PLift.up (Or.inl ⟨by decide⟩)
    | k'' + 1 =>
      match T_to_sum k'' (extract_inl k'' m_prev) with
      | Sum.inl ⟨h_ne⟩ =>
        if h_eq_6 : a (6 * (k'' + 6)) = 4 then
          extract_inl (k'' + 1) (MyProp.dummy (k'' + 1) h_eq_6 (MyProp.intro k'' (Classical.choice h_ne)))
        else
          have h_ne_6 : a (6 * (k'' + 6)) ≠ 4 := h_eq_6
          extract_inl (k'' + 1) (MyProp.intro (k'' + 1) h_ne_6)
      | Sum.inr ⟨h_eq⟩ => extract_inl (k'' + 1) m

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  induction k' with
  | zero => decide
  | succ k'' ih =>
    match T_to_sum (k'' + 1) (pf (k'' + 1)) with
    | Sum.inl ⟨h_ne⟩ => exact Classical.choice h_ne
    | Sum.inr ⟨h_eq⟩ =>
      rcases Classical.em (a (6 * (k'' + 6)) = 4) with h_eq_6 | h_ne_6
      · have m : MyProp (k'' + 1) := MyProp.dummy (k'' + 1) h_eq_6 (MyProp.intro k'' ih)
        match T_to_sum (k'' + 1) (extract_inl (k'' + 1) m) with
        | Sum.inl ⟨h_ne_6⟩ => exact Classical.choice h_ne_6
        | Sum.inr ⟨h_eq_6_new⟩ =>
          have h_empty : MyProp (k'' + 1) → False := by
            intro x
            generalize h_idx : k'' + 1 = idx at x
            induction x with
            | intro k' h_ne =>
              subst h_idx
              exact h_ne h_eq_6_new
            | dummy k' h_eq_5 m_prev ih_prev => exact ih_prev
          exact False.elim (h_empty m)
      · exact h_ne_6
