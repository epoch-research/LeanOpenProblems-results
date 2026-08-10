import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)
def P : Prop := ∀ (n : ℕ), n > 13 → A216265 n > 0

example : P = True ∨ P = False := Classical.propComplete P
example (h : P ≠ False) : P := by
  rcases Classical.propComplete P with hT | hF
  · simpa [hT]
  · exact False.elim (h hF)

-- Can any generic imported fact show P ≠ False?
example : P ≠ False := by
  intro h
  -- h : P = False, equivalent to ¬P; no contradiction available.
  have hnP : ¬ P := by intro hp; simpa [h] using hp
  guard_target = False
  sorry
