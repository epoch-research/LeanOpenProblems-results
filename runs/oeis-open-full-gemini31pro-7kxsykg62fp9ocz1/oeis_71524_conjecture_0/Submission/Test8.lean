import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Prime.Basic

open Matrix Nat

def isPrimeDecidable (n : ℕ) : Decidable n.Prime :=
  inferInstance

def M29 : Matrix (Fin 29) (Fin 29) ℤ := fun i j =>
  let i_idx : ℕ := i.val + 1
  let j_idx : ℕ := j.val + 1
  if (i_idx ^ 2 + j_idx ^ 2).Prime then (1 : ℤ) else (0 : ℤ)

#eval M29 0 0
#eval M29 1 1
