import Mathlib
import Submission.Spec
import Submission.Helper2

open Nat Real intervalIntegral Polynomial

noncomputable def J (n : ℕ) : ℝ := (A340737 n : ℝ) - (A340738 n : ℝ) * exp 1

lemma J_1 : J 1 = 3 - exp 1 := by
  dsimp [J]
  have h1 : A340737 1 = 3 := rfl
  have h2 : A340738 1 = 1 := rfl
  rw [h1, h2]; push_cast; ring

lemma J_3 : J 3 = 19 - 7 * exp 1 := by
  dsimp [J]
  have h1 : A340737 3 = 19 := rfl
  have h2 : A340738 3 = 7 := rfl
  rw [h1, h2]; push_cast; ring

lemma I_1_val : I_k 1 = 3 - exp 1 := by
  have H_int := integral_poly_exp (- X^2 - X - 1 : ℝ[X])
  have H_eq : ∀ x : ℝ, (P_poly 1).eval x * exp (1 - x) = ((- X^2 - X - (1:ℝ[X]) - derivative (- X^2 - X - 1)).eval x) * exp (1 - x) := by
    intro x
    congr 1
    dsimp [P_poly]
    simp
    ring
  have hint_eq : (∫ x in (0:ℝ)..1, (P_poly 1).eval x * exp (1-x)) = ∫ x in (0:ℝ)..1, ((- X^2 - X - (1:ℝ[X]) - derivative (- X^2 - X - 1)).eval x) * exp (1 - x) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact H_eq x
  have h_ik : I_k 1 = ∫ x in (0:ℝ)..1, (P_poly 1).eval x * exp (1 - x) := rfl
  rw [h_ik, hint_eq, H_int]
  have hz : (- X^2 - X - (1:ℝ[X])).eval 0 = -1 := by simp
  have ho : (- X^2 - X - (1:ℝ[X])).eval 1 = -3 := by simp; norm_num
  rw [hz, ho]
  ring

lemma I_2_val : I_k 2 = 7 * exp 1 - 19 := by
  let Q : ℝ[X] := C (1/2) * X^4 + X^3 + C (7/2) * X^2 + C 7 * X + C 7
  have H_int := integral_poly_exp Q
  have H_eq : ∀ x : ℝ, (P_poly 2).eval x * exp (1 - x) = ((Q - derivative Q).eval x) * exp (1 - x) := by
    intro x
    congr 1
    dsimp [P_poly, Q]
    simp
    ring
  have hint_eq : (∫ x in (0:ℝ)..1, (P_poly 2).eval x * exp (1-x)) = ∫ x in (0:ℝ)..1, ((Q - derivative Q).eval x) * exp (1 - x) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact H_eq x
  have h_ik : I_k 2 = ∫ x in (0:ℝ)..1, (P_poly 2).eval x * exp (1 - x) := rfl
  rw [h_ik, hint_eq, H_int]
  have hz : Q.eval 0 = 7 := by dsimp [Q]; simp
  have ho : Q.eval 1 = 19 := by dsimp [Q]; simp; norm_num
  rw [hz, ho]
