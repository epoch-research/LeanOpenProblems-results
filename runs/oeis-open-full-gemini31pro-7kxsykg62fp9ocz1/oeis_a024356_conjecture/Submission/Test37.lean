import Mathlib
open Matrix Nat

noncomputable def A024356 (n : ℕ) : ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n => (Nat.nth Nat.Prime (i.val + j.val) : ℤ))

-- Let's extract the first 7 primes and prove their values
lemma p0 : Nat.nth Nat.Prime 0 = 2 := by sorry
lemma p1 : Nat.nth Nat.Prime 1 = 3 := by sorry
lemma p2 : Nat.nth Nat.Prime 2 = 5 := by sorry
lemma p3 : Nat.nth Nat.Prime 3 = 7 := by sorry
lemma p4 : Nat.nth Nat.Prime 4 = 11 := by sorry
lemma p5 : Nat.nth Nat.Prime 5 = 13 := by sorry
lemma p6 : Nat.nth Nat.Prime 6 = 17 := by sorry

lemma a4_eq_0 : A024356 4 = 0 := by
  sorry
