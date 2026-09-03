import Submission.MatrixCertificates

/-! A checked matrix control at the critical rates (4,3), not a proof
of Erdős 406. -/
namespace Erdos406MatrixControl
open Erdos406Matrix Erdos406GroupedCertificate
open scoped BigOperators Matrix
noncomputable section

def A (d : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := !![3, 3 * d; 0, 1]
def H (c : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := !![4, 3 * c; 0, 1]
def v (n : ℕ) : Fin 2 → ℝ := ![3 * n, 1]
def u : Fin 2 → ℝ := ![1, 1]
def ell : Fin 2 → ℝ := ![1, 3 / 2]

def dynamics : Dynamics (Fin 2) where
  A := A
  v := v
  nonneg := by
    intro d hd i j
    fin_cases i <;> fin_cases j <;> norm_num [A]
  initial_nonneg := by
    intro i
    fin_cases i <;> norm_num [v]
  recurrence := by
    intro n hn
    have he : (n : ℝ) = 3 * (n / 3 : ℕ) + (n % 3 : ℕ) := by
      exact_mod_cast (by omega : n = 3 * (n / 3) + n % 3)
    funext i
    fin_cases i <;> norm_num [A,v,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    nlinarith
  H := H
  seed := by
    intro c hc i
    fin_cases i <;> norm_num [H,v,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  step := by
    intro c d e cp hc hd he hcp har i j
    have hr : 4 * (d : ℝ) + cp = 3 * c + e := by exact_mod_cast har
    fin_cases i <;> fin_cases j <;>
      norm_num [A,H,Matrix.mul_apply,Fin.sum_univ_two]
    nlinarith

lemma u_nonneg : (0 : Fin 2 → ℝ) ≤ u := by
  intro i
  fin_cases i <;> norm_num [u]

lemma u_le_ell : u ≤ ell := by
  intro i
  fin_cases i <;> norm_num [u,ell]

lemma finish (j : Fin 2) : 4 * u j ≤ Matrix.vecMul u (dynamics.H 1) j := by
  fin_cases j <;> norm_num [dynamics,u,H,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

lemma good_step (d : ℕ) (hd : d < 2) (j : Fin 2) :
    Matrix.vecMul ell (dynamics.A d) j ≤ 3 * ell j := by
  interval_cases d <;> fin_cases j <;>
    norm_num [dynamics,ell,A,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

lemma observable (n : ℕ) : u ⬝ᵥ dynamics.v n = 3 * n + 1 := by
  norm_num [dynamics,u,v,dotProduct,Fin.sum_univ_two]

theorem control_grows (n : ℕ) :
    4 * (u ⬝ᵥ dynamics.v n) ≤ u ⬝ᵥ dynamics.v (4 * n + 1) :=
  dynamics.scalar_growth u 4 u_nonneg finish n

theorem control_good_bound (n : ℕ) (hn : Good n) :
    u ⬝ᵥ dynamics.v n ≤ (3 / 2 : ℝ) * 3 ^ (Nat.digits 3 n).length := by
  have hh := (dot_mono_left u_le_ell (dynamics.value_nonneg n)).trans
    (dynamics.good_rate ell 3 (by norm_num) good_step n hn)
  simpa [dynamics,ell,v,dotProduct,Fin.sum_univ_two,mul_comm] using hh

theorem control_not_subcritical :
    ¬ Real.log 3 * Real.log 4 < Real.log 4 * Real.log 3 := by
  rw [mul_comm (Real.log 3) (Real.log 4)]
  exact lt_irrefl _

#print axioms control_grows
#print axioms control_good_bound
#print axioms control_not_subcritical
end
end Erdos406MatrixControl
