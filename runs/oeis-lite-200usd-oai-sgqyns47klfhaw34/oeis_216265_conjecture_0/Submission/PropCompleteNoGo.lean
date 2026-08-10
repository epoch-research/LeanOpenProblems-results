import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

def P : Prop := ∀ n : ℕ, n > 13 → A216265 n > 0

example : Decidable P := Classical.propDecidable P
example : P ∨ ¬ P := Classical.em P
example : P = True ∨ P = False := Classical.propComplete P

example : P := by
  classical
  rcases Classical.propComplete P with hp | hp
  · simpa [hp]
  · -- impossible to close without proving False
    change P
    rw [hp]
    fail_if_success exact False.elim (by contradiction)
    sorry
