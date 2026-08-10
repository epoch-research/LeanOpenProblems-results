import FormalConjectures.Util.Answer
import Mathlib.Data.Nat.Basic

set_option google.answer "always_true"

def my_prop (P : Prop) : Prop := (P ↔ answer(sorry))

def my_cast (P : Prop) (h : my_prop P) : P := h.mpr trivial

theorem test_thm3 : ∃ x : ℕ, x = 1 := by
  have h : my_prop (∃ x : ℕ, x = 1) := answer(sorry)
  exact my_cast (∃ x : ℕ, x = 1) h

#print axioms test_thm3