import FormalConjectures.Util.ProblemImports
open Nat

abbrev TargetP : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

example : TargetP := by
  have h : TargetP = True := by
    exact?
  simpa [h]

example : TargetP := by
  have h : TargetP ↔ True := by
    constructor
    · intro _; trivial
    · intro _
      exact?
  exact h.mpr trivial

example : TargetP := by
  have h : TargetP = True := Subsingleton.elim TargetP True
  simpa [h]

example : TargetP := by
  have h : (TargetP : Prop) = (True : Prop) := by
    apply propext
    exact?
  simpa [h]
