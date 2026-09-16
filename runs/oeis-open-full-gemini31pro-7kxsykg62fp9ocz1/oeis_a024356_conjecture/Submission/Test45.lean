import Mathlib
open Matrix Nat

noncomputable def A024356 (n : ℕ) : ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n => (Nat.nth Nat.Prime (i.val + j.val) : ℤ))

lemma p_vals :
  (Nat.nth Nat.Prime 0 = 2) ∧
  (Nat.nth Nat.Prime 1 = 3) ∧
  (Nat.nth Nat.Prime 2 = 5) ∧
  (Nat.nth Nat.Prime 3 = 7) ∧
  (Nat.nth Nat.Prime 4 = 11) ∧
  (Nat.nth Nat.Prime 5 = 13) ∧
  (Nat.nth Nat.Prime 6 = 17) := by
  sorry
