import Mathlib
open Matrix Nat

noncomputable def A024356 (n : ℕ) : ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n => (Nat.nth Nat.Prime (i.val + j.val) : ℤ))

theorem a0 : A024356 0 = 1 := by
  dsimp [A024356]
  exact det_isEmpty

