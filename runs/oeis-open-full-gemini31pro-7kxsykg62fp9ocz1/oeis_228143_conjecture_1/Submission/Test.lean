import Submission.Spec
open BigOperators Matrix Nat PowerSeries

#eval A005259' 0
#eval A005259' 1
#eval A005259' 2

def a_comp (n : ℕ) : ℕ :=
  let dim := Fin (n + 1)
  let M : Matrix dim dim ℤ :=
    Matrix.of fun i j => (A005259' (i.val + j.val) : ℤ)
  M.det.natAbs

#eval a_comp 0
#eval a_comp 1
#eval a_comp 2
