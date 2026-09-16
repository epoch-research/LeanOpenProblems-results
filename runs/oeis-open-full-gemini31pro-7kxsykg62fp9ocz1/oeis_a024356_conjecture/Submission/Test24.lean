import Mathlib
open Matrix Nat

noncomputable def A024356 (n : ℕ) : ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n => (Nat.nth Nat.Prime (i.val + j.val) : ℤ))

lemma eval_a5 : A024356 5 = 288 := by
  sorry
