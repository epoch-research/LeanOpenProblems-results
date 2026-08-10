import Mathlib

def a (n : ℕ) : ℕ := 0

inductive MyProp (k' : ℕ) : Prop where
  | intro : (a (6 * (k' + 5)) ≠ 4) → MyProp k'

partial def pf_nonempty (k' : ℕ) : PLift (Nonempty (MyProp k')) := pf_nonempty k'

instance (k' : ℕ) : Nonempty (PLift (MyProp k')) := by
  rcases (pf_nonempty k') with ⟨h_ne⟩
  exact Nonempty.map PLift.up h_ne

partial def pf (k' : ℕ) : PLift (MyProp k') := pf k'

theorem pf_eq (k' : ℕ) (h : a (6 * (k' + 5)) ≠ 4) : pf k' = PLift.up (MyProp.intro h) := rfl
