import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

inductive MyProp : ℕ → Type
  | intro : ∀ (k' : ℕ), (a (6 * (k' + 5))  ≠ 4) → MyProp k'
  | dummy : ∀ (k' : ℕ), (PLift (a (6 * (k' + 5))  = 4) × MyProp (k' - 1)) → MyProp k'
  | dummy2 : ∀ (k' : ℕ), (a (6 * (k' + 5))  ≠ 4) → MyProp k'

instance (k' : ℕ) : Nonempty (MyProp k') := by
  induction k' with
  | zero =>
    have h_ne : a 30 ≠ 4 := by decide
    exact ⟨MyProp.intro 0 h_ne⟩
  | succ k'' ih =>
    rcases Classical.em (a (6 * (k'' + 6)) = 4) with h | h
    · exact ⟨MyProp.dummy (k'' + 1) ⟨⟨h⟩, Classical.choice ih⟩⟩
    · exact ⟨MyProp.intro (k'' + 1) h⟩

partial def pf (k' : ℕ) : MyProp k' := pf k'

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

partial def extract_inl (k' : ℕ) (m : MyProp k') : T k' :=
  match m with
  | MyProp.intro _ h_ne => PLift.up (Or.inl ⟨h_ne⟩)
  | MyProp.dummy2 _ h_ne => PLift.up (Or.inl ⟨h_ne⟩)
  | MyProp.dummy _ ⟨⟨_⟩, m_prev⟩ =>
    match k' with
    | 0 => PLift.up (Or.inl ⟨by decide⟩)
    | k'' + 1 =>
      match T_to_sum k'' (extract_inl k'' m_prev) with
      | Sum.inl ⟨h_ne⟩ => extract_inl (k'' + 1) (MyProp.intro (k'' + 1) (Classical.choice h_ne))
      | Sum.inr ⟨h_eq⟩ => extract_inl (k'' + 1) m
