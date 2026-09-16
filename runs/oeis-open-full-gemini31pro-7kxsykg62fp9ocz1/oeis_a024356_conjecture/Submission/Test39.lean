import Mathlib
open Matrix Nat

def comp_primes : List ℤ := [2, 3, 5, 7, 11, 13, 17]

def comp_matrix : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of (fun i j => comp_primes.getD (i.val + j.val) 0)

lemma comp_matrix_det : comp_matrix.det = 0 := by decide

