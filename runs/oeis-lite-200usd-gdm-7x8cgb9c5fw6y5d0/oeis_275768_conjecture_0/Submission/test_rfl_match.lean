import Mathlib

def a (n : ℕ) : ℕ := 0

inductive MyProp (k' : ℕ) : Prop where
  | intro : (a (6 * (k' + 5)) ≠ 4) → MyProp k'

def T (k' : ℕ) : Type := PLift (MyProp k' ∨ (a (6 * (k' + 5)) = 4))

instance (k' : ℕ) : Nonempty (T k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨⟨Or.inr h⟩⟩
  · exact ⟨⟨Or.inl (MyProp.intro h)⟩⟩

partial def pf (k' : ℕ) : T k' := pf k'

theorem pf_eq (k' : ℕ) (h : a (6 * (k' + 5)) ≠ 4) : pf k' = PLift.up (Or.inl (MyProp.intro h)) := rfl

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  induction k' with
  | zero => decide
  | succ k'' ih =>
    -- pf (k'' + 1) is definitionally equal to PLift.up (Or.inl (MyProp.intro (main_case (k'' + 1))))
    have x := pf (k'' + 1)
    -- So x.down is definitionally equal to Or.inl (MyProp.intro (main_case (k'' + 1)))
    -- Let's match on x.down with only the Or.inl constructor!
    exact match x.down with
    | Or.inl (MyProp.intro h) => h


#print axioms main_case