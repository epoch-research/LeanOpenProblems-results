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

mutual
  partial def main_case_impl (k' : ℕ) : PLift (a (6 * (k' + 5)) ≠ 4) :=
    match k' with
    | 0 => PLift.up (by decide)
    | k'' + 1 =>
      -- pf (k'' + 1) is definitionally equal to PLift.up (Or.inl (MyProp.intro (main_case_impl (k'' + 1)).down))
      match (pf (k'' + 1)).down with
      | Or.inl (MyProp.intro h) => PLift.up h
end
