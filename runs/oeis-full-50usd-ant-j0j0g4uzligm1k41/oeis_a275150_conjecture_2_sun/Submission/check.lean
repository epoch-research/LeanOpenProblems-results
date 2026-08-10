import Mathlib

-- representability predicate matching the conjecture's S for (1,1,1,2,2,3)
def repble (n : ℕ) : Prop := ∃ x y z : ℕ, n = 1*x^2 + 1*y^2 + 1*z^3

-- check 7 is NOT representable, and some large values ARE
example : ¬ (∃ x ∈ Finset.range 4, ∃ y ∈ Finset.range 4, ∃ z ∈ Finset.range 4, 7 = 1*x^2+1*y^2+1*z^3) := by native_decide
example : ∃ x ∈ Finset.range 2300, ∃ y ∈ Finset.range 2300, ∃ z ∈ Finset.range 180, (5042632:ℕ) = 1*x^2+1*y^2+1*z^3 := by native_decide
example : ∃ x ∈ Finset.range 60000, ∃ y ∈ Finset.range 60000, ∃ z ∈ Finset.range 500, (99999999:ℕ) = 1*x^2+1*y^2+1*z^3 := by native_decide
