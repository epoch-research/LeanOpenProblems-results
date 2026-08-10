import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

inductive MyProp (k' : ℕ) : Type where
  | intro : (a (6 * (k' + 5)) ≠ 4) → MyProp k'
  | dummy : (a (6 * (k' + 5)) = 4) → MyProp k'

instance (k' : ℕ) : Nonempty (MyProp k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨MyProp.dummy h⟩
  · exact ⟨MyProp.intro h⟩

partial def pf (k' : ℕ) : MyProp k' := pf k'

instance (k'' : ℕ) (h_val2 : a (6 * (k'' + 6)) = 4) :
    Nonempty (PLift ((∃ h : a (6 * (k'' + 6)) ≠ 4, pf (k'' + 1) = MyProp.intro h) ∨ pf (k'' + 1) = MyProp.dummy h_val2)) := by
  rcases pf (k'' + 1) with h_intro | h_dummy
  · exact ⟨⟨Or.inl ⟨h_intro, rfl⟩⟩⟩
  · exact ⟨⟨Or.inr rfl⟩⟩

partial def pf_eq (k'' : ℕ) (h_val2 : a (6 * (k'' + 6)) = 4) :
    PLift ((∃ h : a (6 * (k'' + 6)) ≠ 4, pf (k'' + 1) = MyProp.intro h) ∨ pf (k'' + 1) = MyProp.dummy h_val2) :=
  pf_eq k'' h_val2
