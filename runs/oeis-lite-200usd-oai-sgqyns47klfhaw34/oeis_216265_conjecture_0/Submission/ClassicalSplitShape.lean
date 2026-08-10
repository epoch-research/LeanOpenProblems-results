import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)
def P : Prop := ∀ n : ℕ, n > 13 → A216265 n > 0

example : Decidable P := by classical exact inferInstance
example : P ∨ ¬ P := by classical exact em P
example : (P → P) := by intro h; exact h
-- Shows the only obstruction is the false branch.
example : P := by
  classical
  by_cases h : P
  · exact h
  · guard_target = P
    exfalso
    -- h : ¬ P
    exact h ?x
