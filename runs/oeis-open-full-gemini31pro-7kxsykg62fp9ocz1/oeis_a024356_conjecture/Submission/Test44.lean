import Mathlib
open Matrix Nat

noncomputable def A024356 (n : ℕ) : ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n => (Nat.nth Nat.Prime (i.val + j.val) : ℤ))

-- Can we evaluate A024356 1?
-- Nat.nth Nat.Prime is not computable, so we can't use #eval.
