import Mathlib
open Matrix Nat

noncomputable def A024356 (n : ℕ) : ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n => (Nat.nth Nat.Prime (i.val + j.val) : ℤ))

lemma p0 : Nat.nth Nat.Prime 0 = 2 := by sorry

lemma a4_zero : A024356 4 = 0 := by
  sorry
