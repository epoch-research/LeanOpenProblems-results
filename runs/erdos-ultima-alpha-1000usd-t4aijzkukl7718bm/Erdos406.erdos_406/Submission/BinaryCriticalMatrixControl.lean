import Submission.BinaryCriticalMatrixCertificates

/-! A zero-seed control with a real Jordan block, but no positive Jordan
component on powers. It is NOT a finiteness certificate. -/
namespace Erdos406BinaryCriticalMatrixControl
open Erdos406BinaryCriticalMatrix
open scoped BigOperators Matrix
noncomputable section

def A (d : ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  if d=0 then !![1,0,0,0; 0,2,2,0; 0,0,2,0; 0,0,0,0]
  else !![0,0,0,0; 0,0,0,0; 0,0,0,0; 16,0,0,0]
def H (c : ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  if c=0 then !![1,0,0,0; 0,0,0,0; 0,0,0,0; 0,0,0,0]
  else if c=1 then !![0,0,0,0; 0,0,0,0; 0,0,0,0; 16,0,0,0]
  else 0
def v0 : Fin 4 → ℝ := ![1,0,0,0]
def v (n : ℕ) : Fin 4 → ℝ := evalNat A v0 n
def u : Fin 4 → ℝ := ![6,1,0,1]
def r : Fin 4 → ℝ := ![0,1,0,0]
def s : Fin 4 → ℝ := ![0,0,1,0]

private lemma v_zero : v 0=v0 := evalNat_zero A v0
private lemma v_one : v 1=![0,0,0,16] := by
  rw [v,evalNat_pos A v0 1 (by decide)]
  funext i
  fin_cases i <;> norm_num [A,v0,evalNat_zero,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
private lemma v_two : v 2=0 := by
  have hh := evalNat_pos A v0 2 (by decide)
  change v 2=A (2%2) *ᵥ v (2/2) at hh
  rw [hh]
  funext i
  fin_cases i <;> norm_num [v_one,A,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

def dynamics : Dynamics (Fin 4) where
  A := A
  v := v
  nonneg := by
    intro d hd i j
    interval_cases d <;> fin_cases i <;> fin_cases j <;> norm_num [A]
  initial_nonneg := by
    rw [v_zero]
    intro i
    fin_cases i <;> norm_num [v0]
  recurrence := evalNat_pos A v0
  H := H
  seed := by
    intro c hc i
    interval_cases c <;> fin_cases i <;>
      norm_num [v_zero,v_one,v_two,H,v0,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  step := by
    intro c d e cp hc hd he hcp har i j
    interval_cases c <;> interval_cases d <;> interval_cases e <;> interval_cases cp <;>
      norm_num at har <;> fin_cases i <;> fin_cases j <;>
      norm_num [A,H,Matrix.mul_apply,Fin.sum_univ_succ]

lemma u_nonneg : (0:Fin 4 → ℝ)≤u := by intro i; fin_cases i <;> norm_num [u]
lemma r_nonneg : (0:Fin 4 → ℝ)≤r := by intro i; fin_cases i <;> norm_num [r]
lemma r_le_u : r≤u := by intro i; fin_cases i <;> norm_num [r,u]
lemma finish : ∀ c<2, ∀ j, Matrix.vecMul u (dynamics.H c) j≤3*u j := by
  intro c hc j
  interval_cases c <;> fin_cases j <;>
    norm_num [dynamics,u,H,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]
lemma jordan_first : ∀ j, 2*r j+2*s j≤Matrix.vecMul r (dynamics.A 0) j := by
  intro j; fin_cases j <;> norm_num [dynamics,r,s,A,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]
lemma jordan_second : ∀ j, 2*s j≤Matrix.vecMul s (dynamics.A 0) j := by
  intro j; fin_cases j <;> norm_num [dynamics,s,A,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

lemma construction_bound (n d : ℕ) (hd : d<2) :
    u ⬝ᵥ dynamics.v (3*n+d)≤3*(u ⬝ᵥ dynamics.v n) :=
  dynamics.construction u u_nonneg finish n d hd
lemma good_bound (n : ℕ) (hg : Nat.digits 3 n ⊆ [0,1]) :
    u ⬝ᵥ dynamics.v n≤6*(3:ℝ)^(Nat.digits 3 n).length := by
  have hh := good_upper (fun n => u ⬝ᵥ dynamics.v n) construction_bound n hg
  simpa [dynamics,v_zero,u,v0,dotProduct,Fin.sum_univ_succ,mul_comm] using hh
lemma zero_jordan_seed : s ⬝ᵥ dynamics.v 1=0 := by
  norm_num [dynamics,v_one,s,dotProduct,Fin.sum_univ_succ]
lemma not_positive_seed : ¬ 0<s ⬝ᵥ dynamics.v 1 := by rw [zero_jordan_seed]; exact lt_irrefl _

end
end Erdos406BinaryCriticalMatrixControl
