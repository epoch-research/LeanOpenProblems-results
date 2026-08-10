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

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  induction k' with
  | zero => decide
  | succ k'' ih =>
    rcases Classical.em (a (6 * (k'' + 6)) = 4) with h_eq_6 | h_ne_6
    · have m : MyProp (k'' + 1) := Classical.choice (by infer_instance)
      have h_false : False := by
        cases m with
        | intro _ h_ne => exact h_ne h_eq_6
        | dummy _ h_eq_5 m_prev => exact ih h_eq_5
      exact False.elim h_false
    · exact h_ne_6
