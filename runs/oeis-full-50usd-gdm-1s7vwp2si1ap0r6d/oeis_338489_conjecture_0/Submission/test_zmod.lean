import FormalConjectures.Util.ProblemImports
open Nat

def is_triangular (x : ℕ) : Prop :=
  ∃ k : ℕ, x = k * (k + 1) / 2

lemma k_mul_k_add_one_even (k : ℕ) : 2 ∣ k * (k + 1) := by
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · use m * (2 * m + 1)
    ring
  · use (2 * m + 1) * (m + 1)
    ring

lemma k_mul_k_add_one_div_two_mul_two (k : ℕ) : (k * (k + 1) / 2) * 2 = k * (k + 1) := by
  have hdvd : 2 ∣ k * (k + 1) := k_mul_k_add_one_even k
  exact Nat.div_mul_cancel hdvd

lemma not_triangular_of_not_square (x : ℕ) (h : ¬ ∃ y : ℕ, y * y = 8 * x + 1) : ¬ is_triangular x := by
  rintro ⟨k, rfl⟩
  apply h
  use 2 * k + 1
  have : 8 * (k * (k + 1) / 2) + 1 = (2 * k + 1) * (2 * k + 1) := by
    have : 8 * (k * (k + 1) / 2) = 4 * ((k * (k + 1) / 2) * 2) := by ring
    rw [this, k_mul_k_add_one_div_two_mul_two]
    ring
  exact this.symm

lemma not_square_of_not_square_zmod (x : ℕ) (p : ℕ) [Fact (Nat.Prime p)] (h : ¬ ∃ y : ZMod p, y^2 = (x : ZMod p)) :
  ¬ ∃ y : ℕ, y * y = x := by
  rintro ⟨y, hy⟩
  apply h
  use (y : ZMod p)
  have : ((y : ZMod p) ^ 2) = (((y * y : ℕ) : ZMod p)) := by
    simp only [sq, Nat.cast_mul]
  rw [this, hy]

instance instPrime11 : Fact (Nat.Prime 11) := ⟨by decide⟩
instance instPrime13 : Fact (Nat.Prime 13) := ⟨by decide⟩
instance instPrime17 : Fact (Nat.Prime 17) := ⟨by decide⟩
instance instPrime19 : Fact (Nat.Prime 19) := ⟨by decide⟩
instance instPrime23 : Fact (Nat.Prime 23) := ⟨by decide⟩

theorem not_triangular_6 : ¬ is_triangular (factorial 6) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 11, y^2 = (8 * factorial 6 + 1 : ZMod 11) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 6 + 1) 11 h_zmod

theorem not_triangular_7 : ¬ is_triangular (factorial 7) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 11, y^2 = (8 * factorial 7 + 1 : ZMod 11) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 7 + 1) 11 h_zmod

theorem not_triangular_8 : ¬ is_triangular (factorial 8) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 11, y^2 = (8 * factorial 8 + 1 : ZMod 11) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 8 + 1) 11 h_zmod

theorem not_triangular_9 : ¬ is_triangular (factorial 9) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 13, y^2 = (8 * factorial 9 + 1 : ZMod 13) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 9 + 1) 13 h_zmod

theorem not_triangular_10 : ¬ is_triangular (factorial 10) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 17, y^2 = (8 * factorial 10 + 1 : ZMod 17) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 10 + 1) 17 h_zmod

theorem not_triangular_11 : ¬ is_triangular (factorial 11) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 19, y^2 = (8 * factorial 11 + 1 : ZMod 19) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 11 + 1) 19 h_zmod

theorem not_triangular_12 : ¬ is_triangular (factorial 12) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 13, y^2 = (8 * factorial 12 + 1 : ZMod 13) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 12 + 1) 13 h_zmod

theorem not_triangular_13 : ¬ is_triangular (factorial 13) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 19, y^2 = (8 * factorial 13 + 1 : ZMod 19) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 13 + 1) 19 h_zmod

theorem not_triangular_14 : ¬ is_triangular (factorial 14) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 17, y^2 = (8 * factorial 14 + 1 : ZMod 17) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 14 + 1) 17 h_zmod

theorem not_triangular_15 : ¬ is_triangular (factorial 15) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 19, y^2 = (8 * factorial 15 + 1 : ZMod 19) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 15 + 1) 19 h_zmod

theorem not_triangular_16 : ¬ is_triangular (factorial 16) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 17, y^2 = (8 * factorial 16 + 1 : ZMod 17) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 16 + 1) 17 h_zmod

theorem not_triangular_17 : ¬ is_triangular (factorial 17) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 23, y^2 = (8 * factorial 17 + 1 : ZMod 23) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 17 + 1) 23 h_zmod
