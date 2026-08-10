import Mathlib

def a (n : ℕ) : ℕ := 0

def T (k' : ℕ) : Type := PLift (Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ (a (6 * (k' + 5)) = 4))

def HRecType (k' : ℕ) (m : ℕ) : Type :=
  PLift (Nonempty (a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (m + 5)) = 4 ∧ (Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ a (6 * (k' + 5)) = 4)))

instance (k' : ℕ) : Nonempty (T k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨⟨Or.inr h⟩⟩
  · exact ⟨⟨Or.inl ⟨h⟩⟩⟩

instance (k' m : ℕ) : Nonempty (HRecType k' m) := by
  rcases Classical.em (a (6 * (m + 5)) = 4) with h | h
  · rcases Classical.em (a (6 * (k' + 5)) = 4) with h2 | h2
    · exact ⟨⟨Or.inr ⟨h, Or.inr h2⟩⟩⟩
    · exact ⟨⟨Or.inr ⟨h, Or.inl ⟨h2⟩⟩⟩⟩
  · exact ⟨⟨Or.inl ⟨h⟩⟩⟩

-- Let's define the decidability instances
instance (n : ℕ) : Decidable (a n = 4) := Nat.decEq (a n) 4

instance (n : ℕ) : Decidable (a n ≠ 4) := Not.Decidable

instance (n : ℕ) : Decidable (Nonempty (a n ≠ 4)) := by
  rcases Classical.em (a n ≠ 4) with h | h
  · exact Decidable.isTrue ⟨h⟩
  · exact Decidable.isFalse (fun ⟨h2⟩ => h h2)

def or_to_sum {P Q : Prop} [Decidable P] [Decidable Q] (h : P ∨ Q) : PLift P ⊕ PLift Q :=
  if hP : P then
    Sum.inl ⟨hP⟩
  else
    have hQ : Q := h.resolve_left hP
    Sum.inr ⟨hQ⟩

def T_to_sum (k' : ℕ) (t : T k') : PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  or_to_sum t.down

def HRec_to_sum (k' : ℕ) (m : ℕ) (t : HRecType k' m) :
    PLift (Nonempty (a (6 * (m + 5)) ≠ 4)) ⊕ PLift (a (6 * (m + 5)) = 4 ∧ (Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ a (6 * (k' + 5)) = 4)) :=
  or_to_sum t.down

def sub_to_sum (k' : ℕ) (h : Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ a (6 * (k' + 5)) = 4) :
    PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  or_to_sum h
