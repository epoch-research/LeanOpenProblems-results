import FormalConjectures.Util.ProblemImports

open Nat

def is_square (k : ℕ) : Prop := ∃ m : ℕ, k = m^2

theorem oeis_A271510_conjecture_iii (b c : ℕ) :
  (b = 48 ∧ c = 112) ∨
  (b = 63 ∧ c = 7) ∨
  (b = 112 ∧ c = 1008) ∨
  (b = 136 ∧ c = 24) ∨
  (b = 136 ∧ c = 216) ∨
  (b = 360 ∧ c = 40) ∨
  (b = 840 ∧ c = 280) ∨
  (b = 1008 ∧ c = 112) →
  ∀ n : ℕ, ∃ x y z w : ℕ,
    x^2 + y^2 + z^2 + w^2 = n ∧
    x ≥ y ∧
    is_square (9*x^2 + b*y^2 + c*z^2)
  := by sorry

theorem oeis_A271510_conjecture_iii.disproof : ¬ (type_of% @oeis_A271510_conjecture_iii) := sorry
