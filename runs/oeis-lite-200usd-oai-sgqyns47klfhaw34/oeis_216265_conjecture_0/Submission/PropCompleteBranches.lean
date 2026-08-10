import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

def P : Prop := ∀ (n : ℕ), n > 13 → A216265 n > 0

example : P ∨ ¬ P := by classical exact em P
example : (P = True) ∨ (P = False) := Classical.propComplete P

example (h : P = True) : P := by simpa [h]
example (h : P = False) : ¬ P := by intro hp; simpa [h] using hp

-- The hard branches:
example : P := by
  cases Classical.propComplete P with
  | inl h => simpa [P, h]
  | inr h =>
      guard_target = P
      fail_if_success simpa [P, h]
      sorry

example : ¬ P := by
  cases Classical.propComplete P with
  | inl h =>
      guard_target = ¬P
      fail_if_success simpa [P, h]
      sorry
  | inr h => intro hp; simpa [h] using hp
