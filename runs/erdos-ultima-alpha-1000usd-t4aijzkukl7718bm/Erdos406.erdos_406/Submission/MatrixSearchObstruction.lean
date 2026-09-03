import Submission.MatrixGlobalRateObstruction

/-! Checked obstructions for two saved search tables. Not a solution of Erdős 406. -/
namespace Erdos406MatrixSearchObstruction
open Erdos406Matrix Erdos406MatrixGlobalRate
open scoped BigOperators Matrix
noncomputable section

def update4 : ℕ → Matrix (Fin 4) (Fin 4) ℝ
  | 0 => !![299 / 100 , 0 , 0 , 0;
      0 , 299 / 100 , 0 , 0;
      0 , 0 , 1 , 0;
      0 , 0 , 0 , 1]
  | 1 => !![299 / 100 , 0 , 149 / 100 , 3 / 2;
      0 , 299 / 100 , 149 / 100 , 3 / 2;
      0 , 0 , 1 , 1;
      0 , 0 , 0 , 0]
  | _ => !![299 / 100 , 0 , 149 / 50 , 3;
      0 , 299 / 100 , 149 / 50 , 299 / 100;
      0 , 0 , 1 , 1;
      0 , 0 , 0 , 0]

def ell4 : Fin 4 → ℝ := ![1, 1, 600/199, 10]

lemma ell4_dominates : (fun _ : Fin 4 => (1 : ℝ)) ≤ ell4 := by
  intro i; fin_cases i <;> norm_num [ell4]

lemma global_step4 (d : ℕ) (hd : d < 3) (j : Fin 4) :
    Matrix.vecMul ell4 (update4 d) j ≤ (299 / 100 : ℝ) * ell4 j := by
  interval_cases d <;> fin_cases j <;>
    norm_num [ell4, update4, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem table4_no_subcritical_certificate (D : Dynamics (Fin 4))
    (hA : D.A = update4) (lam : ℝ) (hlam : 1 < lam)
    (hzero : 0 < (fun _ => (1 : ℝ)) ⬝ᵥ D.v 0)
    (hfinish : ∀ j, lam ≤ Matrix.vecMul (fun _ => (1 : ℝ)) (D.H 1) j) :
    Real.log lam * Real.log 3 ≤ Real.log (299 / 100) * Real.log 4 := by
  apply global_matrix_rate_obstruction D (fun _ => 1) ell4 lam (299 / 100)
    (by intro i; norm_num) ell4_dominates hzero hlam (by norm_num)
  · simpa only [mul_one] using hfinish
  · simpa only [hA] using global_step4

#print axioms table4_no_subcritical_certificate

def update6 : ℕ → Matrix (Fin 6) (Fin 6) ℝ
  | 0 => !![299 / 100 , 0 , 0 , 0 , 0 , 0;
      0 , 299 / 100 , 0 , 0 , 0 , 0;
      0 , 0 , 299 / 100 , 0 , 1 / 100 , 0;
      0 , 0 , 0 , 299 / 100 , 0 , 0;
      0 , 0 , 0 , 0 , 1 , 0;
      0 , 0 , 0 , 0 , 0 , 1]
  | 1 => !![299 / 100 , 0 , 0 , 0 , 37 / 50 , 3 / 4;
      0 , 299 / 100 , 0 , 0 , 37 / 50 , 3 / 4;
      0 , 0 , 299 / 100 , 0 , 19 / 25 , 3 / 4;
      0 , 0 , 0 , 299 / 100 , 3 / 4 , 3 / 4;
      0 , 0 , 0 , 0 , 1 , 1;
      0 , 0 , 0 , 0 , 0 , 0]
  | _ => !![299 / 100 , 0 , 0 , 0 , 149 / 100 , 3 / 2;
      0 , 299 / 100 , 0 , 0 , 37 / 25 , 149 / 100;
      0 , 0 , 299 / 100 , 0 , 38 / 25 , 3 / 2;
      0 , 0 , 0 , 299 / 100 , 3 / 2 , 3 / 2;
      0 , 0 , 0 , 0 , 1 , 1;
      0 , 0 , 0 , 0 , 0 , 0]

def ell6 : Fin 6 → ℝ := ![1, 1, 1, 1, 600/199, 10]

lemma ell6_dominates : (fun _ : Fin 6 => (1 : ℝ)) ≤ ell6 := by
  intro i; fin_cases i <;> norm_num [ell6]

lemma global_step6 (d : ℕ) (hd : d < 3) (j : Fin 6) :
    Matrix.vecMul ell6 (update6 d) j ≤ (299 / 100 : ℝ) * ell6 j := by
  interval_cases d <;> fin_cases j <;>
    norm_num [ell6, update6, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem table6_no_subcritical_certificate (D : Dynamics (Fin 6))
    (hA : D.A = update6) (lam : ℝ) (hlam : 1 < lam)
    (hzero : 0 < (fun _ => (1 : ℝ)) ⬝ᵥ D.v 0)
    (hfinish : ∀ j, lam ≤ Matrix.vecMul (fun _ => (1 : ℝ)) (D.H 1) j) :
    Real.log lam * Real.log 3 ≤ Real.log (299 / 100) * Real.log 4 := by
  apply global_matrix_rate_obstruction D (fun _ => 1) ell6 lam (299 / 100)
    (by intro i; norm_num) ell6_dominates hzero hlam (by norm_num)
  · simpa only [mul_one] using hfinish
  · simpa only [hA] using global_step6

#print axioms table6_no_subcritical_certificate

end
end Erdos406MatrixSearchObstruction
