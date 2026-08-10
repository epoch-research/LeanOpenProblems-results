import FormalConjectures.Util.ProblemImports
open Nat

lemma not_square_of_not_square_zmod (x : ℕ) (p : ℕ) [Fact (Nat.Prime p)] (h : ¬ ∃ y : ZMod p, y^2 = (x : ZMod p)) :
  ¬ ∃ y : ℕ, y * y = x := by
  rintro ⟨y, hy⟩
  apply h
  use (y : ZMod p)
  have : ((y : ZMod p) ^ 2) = (((y * y : ℕ) : ZMod p)) := by
    simp only [sq, Nat.cast_mul]
  rw [this, hy]

theorem test_decide_11 : ¬ ∃ y : ℕ, y * y = 8 * factorial 11 + 1 := by
  have : Fact (Nat.Prime 19) := ⟨by decide⟩
  have h_zmod : ¬ ∃ y : ZMod 19, y^2 = ((8 * factorial 11 + 1 : ℕ) : ZMod 19) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 11 + 1) 19 h_zmod






