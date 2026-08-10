import FormalConjectures.Util.ProblemImports

open Nat

def in_H0 (m : ℕ) : Prop :=
  ∃ x y z, x^2 + y^2 + z^2 = m ∧ x ≥ y ∧ (x^2 + 8*y^2 + 16*z^2).sqrt * (x^2 + 8*y^2 + 16*z^2).sqrt = x^2 + 8*y^2 + 16*z^2

example : in_H0 3 := by
  use 1, 1, 1
  refine ⟨rfl, by omega, ?_⟩
  have h_sqrt : (1^2 + 8*1^2 + 16*1^2).sqrt = 5 := by
    have : 1^2 + 8*1^2 + 16*1^2 = 5^2 := by rfl
    rw [this]
    exact Nat.sqrt_eq 5
  rw [h_sqrt]
  rfl
