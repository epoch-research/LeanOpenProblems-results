import Mathlib
open Matrix
def my_mat : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => (i.1 + j.1 : ℚ)
#eval my_mat.det
