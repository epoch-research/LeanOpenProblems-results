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

instance instPrime73 : Fact (Nat.Prime 73) := ⟨by decide⟩

theorem not_triangular_61 : ¬ is_triangular (factorial 61) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 73, y^2 = (8 * factorial 61 + 1 : ZMod 73) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 61 + 1) 73 h_zmod
