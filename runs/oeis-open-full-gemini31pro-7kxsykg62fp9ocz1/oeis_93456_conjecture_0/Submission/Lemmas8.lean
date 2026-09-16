import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma hL_ineq (p M : ℕ) (hp : 5 ≤ p) (hM : p ≤ M) :
  p * M - p * p + 2 * p + 2 ≤ p * (M - p + 3) := by
  have H : ((p * M - p * p + 2 * p + 2 : ℕ) : ℤ) ≤ ((p * (M - p + 3) : ℕ) : ℤ) := by
    have h_sub : ((M - p + 3 : ℕ) : ℤ) = (M : ℤ) - p + 3 := by
      rw [Nat.cast_add, Nat.cast_sub hM]
      rfl
    have hp1 : p * p ≤ p * M := Nat.mul_le_mul_left p hM
    have H2 : ((p * M - p * p + 2 * p + 2 : ℕ) : ℤ) = (p : ℤ) * M - (p : ℤ) * p + 2 * p + 2 := by
      push_cast [Nat.cast_sub hp1]
      ring
    rw [H2]
    have : ((p * (M - p + 3) : ℕ) : ℤ) = (p : ℤ) * ((M - p + 3 : ℕ) : ℤ) := by push_cast; rfl
    rw [this, h_sub]
    nlinarith
  exact Nat.cast_le.mp H
