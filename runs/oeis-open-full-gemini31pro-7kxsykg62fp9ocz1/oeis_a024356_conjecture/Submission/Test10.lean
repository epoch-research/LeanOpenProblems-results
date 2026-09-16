import Mathlib
open Matrix Nat

theorem a0 : Matrix.det (Matrix.of fun (i j : Fin 0) => (Nat.nth Nat.Prime (i.val + j.val) : ℤ)) = 1 := by
  exact det_isEmpty

