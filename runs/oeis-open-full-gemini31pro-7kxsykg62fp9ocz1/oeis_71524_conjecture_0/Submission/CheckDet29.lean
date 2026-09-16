import Mathlib

open Matrix Nat

def A29 : Matrix (Fin 14) (Fin 14) ℤ := fun i j =>
  let x := i.val
  let y := j.val
  if ((2*x+2)^2 + (2*y+3)^2).Prime then 1 else 0

-- We won't compute the determinant since 14! is too large for `#eval` natively,
-- but wait, in Lean 4, `#eval` can use `Matrix.det`?
-- 14! = 87 billion, so `#eval A29.det` will timeout.
