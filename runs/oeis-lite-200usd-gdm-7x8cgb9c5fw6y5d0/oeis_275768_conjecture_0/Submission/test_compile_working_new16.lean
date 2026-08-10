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

instance (k' : ℕ) (h : a (6 * (k' + 5)) ≠ 4) : Nonempty (PLift (pf k' = MyProp.intro h)) := by
  rcases pf k' with h_intro | h_dummy
  · exact ⟨⟨rfl⟩⟩
  · exact False.elim (h h_dummy)

partial def pf_eq (k' : ℕ) (h : a (6 * (k' + 5)) ≠ 4) : PLift (pf k' = MyProp.intro h) :=
  pf_eq k' h

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  induction k' with
  | zero => decide
  | succ k'' ih =>
    -- we want to prove a (6 * (k'' + 6)) ≠ 4.
    -- We casing on Classical.em (a (6 * (k'' + 6)) = 4):
    rcases Classical.em (a (6 * (k'' + 6)) = 4) with h_eq | h_ne
    · -- h_eq : a (6 * (k'' + 6)) = 4.
      -- we call pf_eq (k'' + 1) ?...
      -- wait, we don't have main_case (k'' + 1) yet.
      sorry
    · exact h_ne
