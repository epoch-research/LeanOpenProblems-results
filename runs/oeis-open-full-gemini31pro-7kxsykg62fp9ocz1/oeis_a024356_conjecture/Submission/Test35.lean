import Mathlib
open Matrix Nat

def myPrimes : List ℤ := [2, 3, 5, 7, 11, 13, 17]

def myMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of (fun i j => myPrimes.getD (i.val + j.val) 0)

lemma det_myMatrix : myMatrix.det = 0 := by
  decide
