import Mathlib

open Matrix

def myL : Matrix (Fin 2) (Fin 2) ℚ :=
  ![![1, 0], ![2, 1]]

def myU : Matrix (Fin 2) (Fin 2) ℚ :=
  ![![3, 4], ![0, 5]]

lemma L_lower : myL.BlockTriangular OrderDual.toDual := by
  intro i j hij
  revert i j hij
  decide

lemma U_upper : myU.BlockTriangular id := by
  intro i j hij
  revert i j hij
  decide
