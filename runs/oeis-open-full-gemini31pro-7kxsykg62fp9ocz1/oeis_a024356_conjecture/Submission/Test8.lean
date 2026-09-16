import Mathlib
open Matrix Nat

def myPrimes : List ℤ := [2, 3, 5, 7, 11, 13, 17, 19, 23]

def myMatrix : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of (fun i j => myPrimes.getD (i.val + j.val) 0)

#eval myMatrix.det
