import Mathlib
open Matrix Nat

noncomputable def A024356 (n : ℕ) : ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n => (Nat.nth Nat.Prime (i.val + j.val) : ℤ))

lemma p_val (k : ℕ) (p : ℕ) (h : Nat.nth Nat.Prime k = p) : Nat.nth Nat.Prime k = p := h

