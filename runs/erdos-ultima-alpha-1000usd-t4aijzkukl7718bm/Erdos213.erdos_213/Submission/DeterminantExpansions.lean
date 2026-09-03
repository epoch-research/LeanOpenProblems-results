import FormalConjecturesUtil

/-! Finite Laplace expansions with explicit minor matrices, avoiding nested
index embeddings during subsequent symbolic determinant calculations. -/
namespace Erdos213.DeterminantExpansions
set_option maxHeartbeats 0
set_option maxRecDepth 200000
variable {R : Type*} [CommRing R]

def minorTable4 (M : Matrix (Fin 4) (Fin 4) R) : Fin 4 → Matrix (Fin 3) (Fin 3) R :=
  ![!![M 1 1,M 1 2,M 1 3;M 2 1,M 2 2,M 2 3;M 3 1,M 3 2,M 3 3],
    !![M 1 0,M 1 2,M 1 3;M 2 0,M 2 2,M 2 3;M 3 0,M 3 2,M 3 3],
    !![M 1 0,M 1 1,M 1 3;M 2 0,M 2 1,M 2 3;M 3 0,M 3 1,M 3 3],
    !![M 1 0,M 1 1,M 1 2;M 2 0,M 2 1,M 2 2;M 3 0,M 3 1,M 3 2]]

omit [CommRing R] in
lemma minor_table4 (M : Matrix (Fin 4) (Fin 4) R) (j : Fin 4) :
    M.submatrix Fin.succ j.succAbove=minorTable4 M j := by
  fin_cases j
  all_goals ext i k; fin_cases i <;> fin_cases k <;> rfl

lemma det_expand4 (M : Matrix (Fin 4) (Fin 4) R) : M.det=
   M 0 0*Matrix.det (!![M 1 1,M 1 2,M 1 3;M 2 1,M 2 2,M 2 3;M 3 1,M 3 2,M 3 3]) - M 0 1*Matrix.det (!![M 1 0,M 1 2,M 1 3;M 2 0,M 2 2,M 2 3;M 3 0,M 3 2,M 3 3]) + M 0 2*Matrix.det (!![M 1 0,M 1 1,M 1 3;M 2 0,M 2 1,M 2 3;M 3 0,M 3 1,M 3 3]) - M 0 3*Matrix.det (!![M 1 0,M 1 1,M 1 2;M 2 0,M 2 1,M 2 2;M 3 0,M 3 1,M 3 2]) := by
  rw [Matrix.det_succ_row_zero]
  simp_rw [minor_table4]
  norm_num [minorTable4,Fin.sum_univ_succ,Matrix.cons_val]
  ring!

#print axioms det_expand4

def minorTable5 (M : Matrix (Fin 5) (Fin 5) R) : Fin 5 → Matrix (Fin 4) (Fin 4) R :=
  ![!![M 1 1,M 1 2,M 1 3,M 1 4;M 2 1,M 2 2,M 2 3,M 2 4;M 3 1,M 3 2,M 3 3,M 3 4;M 4 1,M 4 2,M 4 3,M 4 4],
    !![M 1 0,M 1 2,M 1 3,M 1 4;M 2 0,M 2 2,M 2 3,M 2 4;M 3 0,M 3 2,M 3 3,M 3 4;M 4 0,M 4 2,M 4 3,M 4 4],
    !![M 1 0,M 1 1,M 1 3,M 1 4;M 2 0,M 2 1,M 2 3,M 2 4;M 3 0,M 3 1,M 3 3,M 3 4;M 4 0,M 4 1,M 4 3,M 4 4],
    !![M 1 0,M 1 1,M 1 2,M 1 4;M 2 0,M 2 1,M 2 2,M 2 4;M 3 0,M 3 1,M 3 2,M 3 4;M 4 0,M 4 1,M 4 2,M 4 4],
    !![M 1 0,M 1 1,M 1 2,M 1 3;M 2 0,M 2 1,M 2 2,M 2 3;M 3 0,M 3 1,M 3 2,M 3 3;M 4 0,M 4 1,M 4 2,M 4 3]]

omit [CommRing R] in
lemma minor_table5 (M : Matrix (Fin 5) (Fin 5) R) (j : Fin 5) :
    M.submatrix Fin.succ j.succAbove=minorTable5 M j := by
  fin_cases j
  all_goals ext i k; fin_cases i <;> fin_cases k <;> rfl

lemma det_expand5 (M : Matrix (Fin 5) (Fin 5) R) : M.det=
   M 0 0*Matrix.det (!![M 1 1,M 1 2,M 1 3,M 1 4;M 2 1,M 2 2,M 2 3,M 2 4;M 3 1,M 3 2,M 3 3,M 3 4;M 4 1,M 4 2,M 4 3,M 4 4]) - M 0 1*Matrix.det (!![M 1 0,M 1 2,M 1 3,M 1 4;M 2 0,M 2 2,M 2 3,M 2 4;M 3 0,M 3 2,M 3 3,M 3 4;M 4 0,M 4 2,M 4 3,M 4 4]) + M 0 2*Matrix.det (!![M 1 0,M 1 1,M 1 3,M 1 4;M 2 0,M 2 1,M 2 3,M 2 4;M 3 0,M 3 1,M 3 3,M 3 4;M 4 0,M 4 1,M 4 3,M 4 4]) - M 0 3*Matrix.det (!![M 1 0,M 1 1,M 1 2,M 1 4;M 2 0,M 2 1,M 2 2,M 2 4;M 3 0,M 3 1,M 3 2,M 3 4;M 4 0,M 4 1,M 4 2,M 4 4]) + M 0 4*Matrix.det (!![M 1 0,M 1 1,M 1 2,M 1 3;M 2 0,M 2 1,M 2 2,M 2 3;M 3 0,M 3 1,M 3 2,M 3 3;M 4 0,M 4 1,M 4 2,M 4 3]) := by
  rw [Matrix.det_succ_row_zero]
  simp_rw [minor_table5]
  norm_num [minorTable5,Fin.sum_univ_succ,Matrix.cons_val]
  ring!

#print axioms det_expand5

def minorTable6 (M : Matrix (Fin 6) (Fin 6) R) : Fin 6 → Matrix (Fin 5) (Fin 5) R :=
  ![!![M 1 1,M 1 2,M 1 3,M 1 4,M 1 5;M 2 1,M 2 2,M 2 3,M 2 4,M 2 5;M 3 1,M 3 2,M 3 3,M 3 4,M 3 5;M 4 1,M 4 2,M 4 3,M 4 4,M 4 5;M 5 1,M 5 2,M 5 3,M 5 4,M 5 5],
    !![M 1 0,M 1 2,M 1 3,M 1 4,M 1 5;M 2 0,M 2 2,M 2 3,M 2 4,M 2 5;M 3 0,M 3 2,M 3 3,M 3 4,M 3 5;M 4 0,M 4 2,M 4 3,M 4 4,M 4 5;M 5 0,M 5 2,M 5 3,M 5 4,M 5 5],
    !![M 1 0,M 1 1,M 1 3,M 1 4,M 1 5;M 2 0,M 2 1,M 2 3,M 2 4,M 2 5;M 3 0,M 3 1,M 3 3,M 3 4,M 3 5;M 4 0,M 4 1,M 4 3,M 4 4,M 4 5;M 5 0,M 5 1,M 5 3,M 5 4,M 5 5],
    !![M 1 0,M 1 1,M 1 2,M 1 4,M 1 5;M 2 0,M 2 1,M 2 2,M 2 4,M 2 5;M 3 0,M 3 1,M 3 2,M 3 4,M 3 5;M 4 0,M 4 1,M 4 2,M 4 4,M 4 5;M 5 0,M 5 1,M 5 2,M 5 4,M 5 5],
    !![M 1 0,M 1 1,M 1 2,M 1 3,M 1 5;M 2 0,M 2 1,M 2 2,M 2 3,M 2 5;M 3 0,M 3 1,M 3 2,M 3 3,M 3 5;M 4 0,M 4 1,M 4 2,M 4 3,M 4 5;M 5 0,M 5 1,M 5 2,M 5 3,M 5 5],
    !![M 1 0,M 1 1,M 1 2,M 1 3,M 1 4;M 2 0,M 2 1,M 2 2,M 2 3,M 2 4;M 3 0,M 3 1,M 3 2,M 3 3,M 3 4;M 4 0,M 4 1,M 4 2,M 4 3,M 4 4;M 5 0,M 5 1,M 5 2,M 5 3,M 5 4]]

omit [CommRing R] in
lemma minor_table6 (M : Matrix (Fin 6) (Fin 6) R) (j : Fin 6) :
    M.submatrix Fin.succ j.succAbove=minorTable6 M j := by
  fin_cases j
  all_goals ext i k; fin_cases i <;> fin_cases k <;> rfl

lemma det_expand6 (M : Matrix (Fin 6) (Fin 6) R) : M.det=
   M 0 0*Matrix.det (!![M 1 1,M 1 2,M 1 3,M 1 4,M 1 5;M 2 1,M 2 2,M 2 3,M 2 4,M 2 5;M 3 1,M 3 2,M 3 3,M 3 4,M 3 5;M 4 1,M 4 2,M 4 3,M 4 4,M 4 5;M 5 1,M 5 2,M 5 3,M 5 4,M 5 5]) - M 0 1*Matrix.det (!![M 1 0,M 1 2,M 1 3,M 1 4,M 1 5;M 2 0,M 2 2,M 2 3,M 2 4,M 2 5;M 3 0,M 3 2,M 3 3,M 3 4,M 3 5;M 4 0,M 4 2,M 4 3,M 4 4,M 4 5;M 5 0,M 5 2,M 5 3,M 5 4,M 5 5]) + M 0 2*Matrix.det (!![M 1 0,M 1 1,M 1 3,M 1 4,M 1 5;M 2 0,M 2 1,M 2 3,M 2 4,M 2 5;M 3 0,M 3 1,M 3 3,M 3 4,M 3 5;M 4 0,M 4 1,M 4 3,M 4 4,M 4 5;M 5 0,M 5 1,M 5 3,M 5 4,M 5 5]) - M 0 3*Matrix.det (!![M 1 0,M 1 1,M 1 2,M 1 4,M 1 5;M 2 0,M 2 1,M 2 2,M 2 4,M 2 5;M 3 0,M 3 1,M 3 2,M 3 4,M 3 5;M 4 0,M 4 1,M 4 2,M 4 4,M 4 5;M 5 0,M 5 1,M 5 2,M 5 4,M 5 5]) + M 0 4*Matrix.det (!![M 1 0,M 1 1,M 1 2,M 1 3,M 1 5;M 2 0,M 2 1,M 2 2,M 2 3,M 2 5;M 3 0,M 3 1,M 3 2,M 3 3,M 3 5;M 4 0,M 4 1,M 4 2,M 4 3,M 4 5;M 5 0,M 5 1,M 5 2,M 5 3,M 5 5]) - M 0 5*Matrix.det (!![M 1 0,M 1 1,M 1 2,M 1 3,M 1 4;M 2 0,M 2 1,M 2 2,M 2 3,M 2 4;M 3 0,M 3 1,M 3 2,M 3 3,M 3 4;M 4 0,M 4 1,M 4 2,M 4 3,M 4 4;M 5 0,M 5 1,M 5 2,M 5 3,M 5 4]) := by
  rw [Matrix.det_succ_row_zero]
  simp_rw [minor_table6]
  norm_num [minorTable6,Fin.sum_univ_succ,Matrix.cons_val]
  ring!

#print axioms det_expand6

end Erdos213.DeterminantExpansions
