import FormalConjecturesUtil

/-! Coefficient extraction for the three-quadratic quintic absorption identity. -/
namespace Erdos322Research.QuinticJointCoefficients
open Polynomial
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private def quad (a b c : ℚ) : ℚ[X] := C a * X^2 + C b * X + C c
private def g (q : Fin 11) (a b c : ℚ) : ℚ :=
  ![c ^ 5, 5 * b * c ^ 4, 10 * b ^ 2 * c ^ 3 + 5 * a * c ^ 4, 10 * b ^ 3 * c ^ 2 + 20 * a * b * c ^ 3, 5 * b ^ 4 * c + 30 * a * b ^ 2 * c ^ 2 + 10 * a ^ 2 * c ^ 3, b ^ 5 + 20 * a * b ^ 3 * c + 30 * a ^ 2 * b * c ^ 2, 5 * a * b ^ 4 + 30 * a ^ 2 * b ^ 2 * c + 10 * a ^ 3 * c ^ 2, 10 * a ^ 2 * b ^ 3 + 20 * a ^ 3 * b * c, 10 * a ^ 3 * b ^ 2 + 5 * a ^ 4 * c, 5 * a ^ 4 * b, a ^ 5] q

private def w (q : Fin 11) : ℚ :=
  ![-6, 0, 60, 0, -240, 0, 480, 0, -480, 0, -64] q

private theorem g_0 (a b c : ℚ) : g 0 a b c = c ^ 5 := rfl
private theorem g_1 (a b c : ℚ) : g 1 a b c = 5 * b * c ^ 4 := rfl
private theorem g_2 (a b c : ℚ) : g 2 a b c = 10 * b ^ 2 * c ^ 3 + 5 * a * c ^ 4 := rfl
private theorem g_3 (a b c : ℚ) : g 3 a b c = 10 * b ^ 3 * c ^ 2 + 20 * a * b * c ^ 3 := rfl
private theorem g_4 (a b c : ℚ) : g 4 a b c = 5 * b ^ 4 * c + 30 * a * b ^ 2 * c ^ 2 + 10 * a ^ 2 * c ^ 3 := rfl
private theorem g_5 (a b c : ℚ) : g 5 a b c = b ^ 5 + 20 * a * b ^ 3 * c + 30 * a ^ 2 * b * c ^ 2 := rfl
private theorem g_6 (a b c : ℚ) : g 6 a b c = 5 * a * b ^ 4 + 30 * a ^ 2 * b ^ 2 * c + 10 * a ^ 3 * c ^ 2 := rfl
private theorem g_7 (a b c : ℚ) : g 7 a b c = 10 * a ^ 2 * b ^ 3 + 20 * a ^ 3 * b * c := rfl
private theorem g_8 (a b c : ℚ) : g 8 a b c = 10 * a ^ 3 * b ^ 2 + 5 * a ^ 4 * c := rfl
private theorem g_9 (a b c : ℚ) : g 9 a b c = 5 * a ^ 4 * b := rfl
private theorem g_10 (a b c : ℚ) : g 10 a b c = a ^ 5 := rfl
private theorem w_0 : w 0 = (-6 : ℚ) := rfl
private theorem w_1 : w 1 = (0 : ℚ) := rfl
private theorem w_2 : w 2 = (60 : ℚ) := rfl
private theorem w_3 : w 3 = (0 : ℚ) := rfl
private theorem w_4 : w 4 = (-240 : ℚ) := rfl
private theorem w_5 : w 5 = (0 : ℚ) := rfl
private theorem w_6 : w 6 = (480 : ℚ) := rfl
private theorem w_7 : w 7 = (0 : ℚ) := rfl
private theorem w_8 : w 8 = (-480 : ℚ) := rfl
private theorem w_9 : w 9 = (0 : ℚ) := rfl
private theorem w_10 : w 10 = (-64 : ℚ) := rfl
def f0 (a0 b0 c0 a1 b1 c1 a2 b2 c2 : ℚ) : ℚ :=
  c0 ^ 5 + c1 ^ 5 + c2 ^ 5 - 6

def f1 (a0 b0 c0 a1 b1 c1 a2 b2 c2 : ℚ) : ℚ :=
  5 * b0 * c0 ^ 4 + 5 * b1 * c1 ^ 4 + 5 * b2 * c2 ^ 4

def f2 (a0 b0 c0 a1 b1 c1 a2 b2 c2 : ℚ) : ℚ :=
  10 * b0 ^ 2 * c0 ^ 3 + 5 * a0 * c0 ^ 4 + 10 * b1 ^ 2 * c1 ^ 3 + 5 * a1 * c1 ^ 4 + 10 * b2 ^ 2 * c2 ^ 3 + 5 * a2 * c2 ^ 4 + 60

def f3 (a0 b0 c0 a1 b1 c1 a2 b2 c2 : ℚ) : ℚ :=
  10 * b0 ^ 3 * c0 ^ 2 + 20 * a0 * b0 * c0 ^ 3 + 10 * b1 ^ 3 * c1 ^ 2 + 20 * a1 * b1 * c1 ^ 3 + 10 * b2 ^ 3 * c2 ^ 2 + 20 * a2 * b2 * c2 ^ 3

def f4 (a0 b0 c0 a1 b1 c1 a2 b2 c2 : ℚ) : ℚ :=
  5 * b0 ^ 4 * c0 + 30 * a0 * b0 ^ 2 * c0 ^ 2 + 10 * a0 ^ 2 * c0 ^ 3 + 5 * b1 ^ 4 * c1 + 30 * a1 * b1 ^ 2 * c1 ^ 2 + 10 * a1 ^ 2 * c1 ^ 3 + 5 * b2 ^ 4 * c2 + 30 * a2 * b2 ^ 2 * c2 ^ 2 + 10 * a2 ^ 2 * c2 ^ 3 - 240

def f5 (a0 b0 c0 a1 b1 c1 a2 b2 c2 : ℚ) : ℚ :=
  b0 ^ 5 + 20 * a0 * b0 ^ 3 * c0 + 30 * a0 ^ 2 * b0 * c0 ^ 2 + b1 ^ 5 + 20 * a1 * b1 ^ 3 * c1 + 30 * a1 ^ 2 * b1 * c1 ^ 2 + b2 ^ 5 + 20 * a2 * b2 ^ 3 * c2 + 30 * a2 ^ 2 * b2 * c2 ^ 2

def f6 (a0 b0 c0 a1 b1 c1 a2 b2 c2 : ℚ) : ℚ :=
  5 * a0 * b0 ^ 4 + 30 * a0 ^ 2 * b0 ^ 2 * c0 + 10 * a0 ^ 3 * c0 ^ 2 + 5 * a1 * b1 ^ 4 + 30 * a1 ^ 2 * b1 ^ 2 * c1 + 10 * a1 ^ 3 * c1 ^ 2 + 5 * a2 * b2 ^ 4 + 30 * a2 ^ 2 * b2 ^ 2 * c2 + 10 * a2 ^ 3 * c2 ^ 2 + 480

def f7 (a0 b0 c0 a1 b1 c1 a2 b2 c2 : ℚ) : ℚ :=
  10 * a0 ^ 2 * b0 ^ 3 + 20 * a0 ^ 3 * b0 * c0 + 10 * a1 ^ 2 * b1 ^ 3 + 20 * a1 ^ 3 * b1 * c1 + 10 * a2 ^ 2 * b2 ^ 3 + 20 * a2 ^ 3 * b2 * c2

def f8 (a0 b0 c0 a1 b1 c1 a2 b2 c2 : ℚ) : ℚ :=
  10 * a0 ^ 3 * b0 ^ 2 + 5 * a0 ^ 4 * c0 + 10 * a1 ^ 3 * b1 ^ 2 + 5 * a1 ^ 4 * c1 + 10 * a2 ^ 3 * b2 ^ 2 + 5 * a2 ^ 4 * c2 - 480

def f9 (a0 b0 c0 a1 b1 c1 a2 b2 c2 : ℚ) : ℚ :=
  5 * a0 ^ 4 * b0 + 5 * a1 ^ 4 * b1 + 5 * a2 ^ 4 * b2

def f10 (a0 b0 c0 a1 b1 c1 a2 b2 c2 : ℚ) : ℚ :=
  a0 ^ 5 + a1 ^ 5 + a2 ^ 5 - 64

theorem coefficient_equations (a0 b0 c0 a1 b1 c1 a2 b2 c2 : ℚ)
    (h : ∀ t : ℚ, (a0*t^2+b0*t+c0)^5 + (a1*t^2+b1*t+c1)^5 +
      (a2*t^2+b2*t+c2)^5 = 6*(1-2*t^2)^5+8*(2*t^2)^5) :
    f0 a0 b0 c0 a1 b1 c1 a2 b2 c2 = 0 ∧
    f1 a0 b0 c0 a1 b1 c1 a2 b2 c2 = 0 ∧
    f2 a0 b0 c0 a1 b1 c1 a2 b2 c2 = 0 ∧
    f3 a0 b0 c0 a1 b1 c1 a2 b2 c2 = 0 ∧
    f4 a0 b0 c0 a1 b1 c1 a2 b2 c2 = 0 ∧
    f5 a0 b0 c0 a1 b1 c1 a2 b2 c2 = 0 ∧
    f6 a0 b0 c0 a1 b1 c1 a2 b2 c2 = 0 ∧
    f7 a0 b0 c0 a1 b1 c1 a2 b2 c2 = 0 ∧
    f8 a0 b0 c0 a1 b1 c1 a2 b2 c2 = 0 ∧
    f9 a0 b0 c0 a1 b1 c1 a2 b2 c2 = 0 ∧
    f10 a0 b0 c0 a1 b1 c1 a2 b2 c2 = 0 := by
  let P : ℚ[X] := quad a0 b0 c0^5 + quad a1 b1 c1^5 + quad a2 b2 c2^5 -
    (6*(1-2*X^2)^5+8*(2*X^2)^5)
  have hp : P = 0 := by
    apply Polynomial.funext
    intro t
    simpa [P, quad] using sub_eq_zero.mpr (h t)
  have he : P = ∑ q : Fin 11,
      C (g q a0 b0 c0 + g q a1 b1 c1 + g q a2 b2 c2 + w q) * X^q.val := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc]
    simp only [g_0, g_1, g_2, g_3, g_4, g_5, g_6, g_7, g_8, g_9, g_10, w_0, w_1, w_2, w_3, w_4, w_5, w_6, w_7, w_8, w_9, w_10]
    norm_num [P, quad, map_add, map_mul, map_pow, map_sub, map_ofNat]
    <;> ring
  have hc (q : Fin 11) : g q a0 b0 c0 + g q a1 b1 c1 + g q a2 b2 c2 + w q = 0 := by
    have H := congrArg (fun p : ℚ[X] => p.coeff q.val) (he.symm.trans hp)
    simp only [finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero, Fin.val_inj] at H
    simpa using H
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have H := hc 0
    simp only [g_0, w_0] at H
    dsimp only [f0]
    linear_combination H
  · have H := hc 1
    simp only [g_1, w_1] at H
    dsimp only [f1]
    linear_combination H
  · have H := hc 2
    simp only [g_2, w_2] at H
    dsimp only [f2]
    linear_combination H
  · have H := hc 3
    simp only [g_3, w_3] at H
    dsimp only [f3]
    linear_combination H
  · have H := hc 4
    simp only [g_4, w_4] at H
    dsimp only [f4]
    linear_combination H
  · have H := hc 5
    simp only [g_5, w_5] at H
    dsimp only [f5]
    linear_combination H
  · have H := hc 6
    simp only [g_6, w_6] at H
    dsimp only [f6]
    linear_combination H
  · have H := hc 7
    simp only [g_7, w_7] at H
    dsimp only [f7]
    linear_combination H
  · have H := hc 8
    simp only [g_8, w_8] at H
    dsimp only [f8]
    linear_combination H
  · have H := hc 9
    simp only [g_9, w_9] at H
    dsimp only [f9]
    linear_combination H
  · have H := hc 10
    simp only [g_10, w_10] at H
    dsimp only [f10]
    linear_combination H

end
end Erdos322Research.QuinticJointCoefficients
