import FormalConjectures.Util.ProblemImports
open Nat

abbrev TargetP2 : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

example (h : TargetP2 = False) : ¬ TargetP2 := by
  intro H
  have : False := by simpa [h] using H
  exact this

-- If P=False, one obtains a concrete bad n classically, but no way to refute it globally.
example (h : TargetP2 = False) :
    ∃ n, n > 0 ∧ ∀ k : ℕ, ¬ (Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) := by
  classical
  have hn : ¬ TargetP2 := by
    intro H
    have : False := by simpa [h] using H
    exact this
  dsimp [TargetP2] at hn
  push_neg at hn
  exact hn
