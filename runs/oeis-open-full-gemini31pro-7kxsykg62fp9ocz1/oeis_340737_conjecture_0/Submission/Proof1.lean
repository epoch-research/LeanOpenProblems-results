import Mathlib
open Nat
open Polynomial Filter Topology
open scoped Polynomial

-- Sequences and bounds
noncomputable def P (k : ℕ) : ℝ[X] := X^k * (1 - X)^k

noncomputable def E_poly (k : ℕ) : ℝ[X] :=
  - X^(k-1) * (1 - X)^(k-1) * (X^2 - (2*k+1 : ℝ[X]) * X + (k : ℝ[X]))

lemma E_eval_zero (k : ℕ) : eval 0 (E_poly (k+2)) = 0 := by unfold E_poly; dsimp; simp
lemma E_eval_one (k : ℕ) : eval 1 (E_poly (k+2)) = 0 := by unfold E_poly; dsimp; simp

noncomputable def Q : ℕ → ℝ[X]
| 0 => 1
| 1 => - X^2 + 3 * X - 3
| (k+2) =>
  let c1 : ℝ[X] := - (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])
  let c2 : ℝ[X] := (k+2:ℝ[X])*(k+1:ℝ[X])
  c1 * Q (k+1) + c2 * Q k + E_poly (k+2)

lemma Q_ind (k : ℕ) (h1 : derivative (Q (k+1)) + Q (k+1) = P (k+1)) (h0 : derivative (Q k) + Q k = P k) :
  derivative (Q (k+2)) + Q (k+2) = P (k+2) := by
  unfold Q
  dsimp
  have H : derivative ((- (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])) * Q (k + 1) + ((k+2:ℝ[X])*(k+1:ℝ[X])) * Q k + E_poly (k + 2)) =
    (- (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])) * derivative (Q (k + 1)) + ((k+2:ℝ[X])*(k+1:ℝ[X])) * derivative (Q k) + derivative (E_poly (k + 2)) := by
    simp [derivative_mul, derivative_add, derivative_sub, derivative_natCast]
  rw [H]
  have H2 : (- (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])) * derivative (Q (k + 1)) +
    ((k+2:ℝ[X])*(k+1:ℝ[X])) * derivative (Q k) + derivative (E_poly (k + 2)) +
    ((- (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])) * Q (k + 1) + ((k+2:ℝ[X])*(k+1:ℝ[X])) * Q k + E_poly (k + 2)) =
    (- (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])) * (derivative (Q (k + 1)) + Q (k + 1)) +
      ((k+2:ℝ[X])*(k+1:ℝ[X])) * (derivative (Q k) + Q k) +
      derivative (E_poly (k + 2)) + E_poly (k + 2) := by ring
  rw [H2, h1, h0]
  unfold P E_poly
  dsimp
  simp [derivative_mul, derivative_pow, derivative_sub, derivative_add, derivative_natCast]
  have h_X2 : (X : ℝ[X])^(k+2) = X^k * X^2 := by ring
  have h_X1 : (X : ℝ[X])^(k+1) = X^k * X := by ring
  have h_Y2 : (1 - X : ℝ[X])^(k+2) = (1-X)^k * (1-X)^2 := by ring
  have h_Y1 : (1 - X : ℝ[X])^(k+1) = (1-X)^k * (1-X) := by ring
  rw [h_X2, h_X1, h_Y2, h_Y1]
  rw [map_ofNat (C : ℝ →+* ℝ[X]) 2]
  ring

lemma Q_eq_P (k : ℕ) : derivative (Q k) + Q k = P k := by
  induction' k using Nat.strong_induction_on with k ih
  rcases k with _ | _ | k
  · dsimp [Q, P]; simp
  · change derivative (- X^2 + 3 * X - 3 : ℝ[X]) + (- X^2 + 3 * X - 3) = X^1 * (1 - X)^1
    simp; ring
  · apply Q_ind k
    · apply ih (k+1) (by omega)
    · apply ih k (by omega)

lemma mvt_poly (k : ℕ) :
  ∃ c ∈ Set.Ioo (0 : ℝ) 1,
    ((Q k).eval 1) * Real.exp 1 - ((Q k).eval 0) = ((P k).eval c) * Real.exp c := by
  have h_deriv : ∀ x, HasDerivAt (fun y => ((Q k).eval y) * Real.exp y) (((P k).eval x) * Real.exp x) x := by
    intro x
    have h1 := ((Q k).hasDerivAt x)
    have h2 := (Real.hasDerivAt_exp x)
    have h3 := HasDerivAt.mul h1 h2
    have h4 : (derivative (Q k)).eval x * Real.exp x + (Q k).eval x * Real.exp x = (P k).eval x * Real.exp x := by
      have h5 : (derivative (Q k)).eval x + (Q k).eval x = (P k).eval x := by
        have h_eq := Q_eq_P k
        rw [← eval_add, h_eq]
      calc (derivative (Q k)).eval x * Real.exp x + (Q k).eval x * Real.exp x
        _ = ((derivative (Q k)).eval x + (Q k).eval x) * Real.exp x := by ring
        _ = (P k).eval x * Real.exp x := by rw [h5]
    exact h4 ▸ h3
  have h_mvt := exists_hasDerivAt_eq_slope (fun y => ((Q k).eval y) * Real.exp y) (fun x => ((P k).eval x) * Real.exp x) (by norm_num : (0:ℝ) < 1)
    (fun x _ => (h_deriv x).continuousAt.continuousWithinAt)
    (fun x _ => h_deriv x)
  rcases h_mvt with ⟨c, hc1, hc2⟩
  use c
  constructor
  · exact hc1
  · have hc3 : (1 : ℝ) - 0 = 1 := by ring
    rw [hc3, div_one] at hc2
    dsimp at hc2
    have hQ0 : Real.exp 0 = 1 := Real.exp_zero
    rw [hQ0, mul_one] at hc2
    exact hc2.symm

lemma P_bound (k : ℕ) (c : ℝ) (hc1 : 0 < c) (hc2 : c < 1) :
  (P k).eval c * Real.exp c ≤ Real.exp 1 / 4^k := by
  unfold P
  simp
  have h1 : c * (1 - c) ≤ 1 / 4 := by
    have h2 : c * (1 - c) = 1/4 - (c - 1/2)^2 := by ring
    rw [h2]
    linarith [sq_nonneg (c - 1/2)]
  have h2 : 0 ≤ c * (1 - c) := by
    have : 0 ≤ c := by linarith
    have : 0 ≤ 1 - c := by linarith
    positivity
  have h3 : (c * (1 - c))^k ≤ (1 / 4)^k := by gcongr
  have h4 : Real.exp c ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    linarith
  have h5 : c^k * (1 - c)^k = (c * (1 - c))^k := by rw [mul_pow]
  rw [h5]
  have h6 : (c * (1 - c))^k * Real.exp c ≤ (1 / 4)^k * Real.exp 1 := by
    have : 0 ≤ (c * (1 - c))^k := by positivity
    have : 0 ≤ Real.exp c := by positivity
    nlinarith
  have h7 : (1 / 4 : ℝ)^k * Real.exp 1 = Real.exp 1 / 4^k := by
    calc (1 / 4 : ℝ)^k * Real.exp 1
      _ = (1^k / 4^k : ℝ) * Real.exp 1 := by rw [div_pow]
      _ = (1 / 4^k) * Real.exp 1 := by rw [one_pow]
      _ = Real.exp 1 / 4^k := by ring
  rw [← h7]
  exact h6

lemma P_pos (k : ℕ) (c : ℝ) (hc1 : 0 < c) (hc2 : c < 1) :
  0 ≤ (P k).eval c * Real.exp c := by
  unfold P
  simp
  have : 0 ≤ c := by linarith
  have : 0 ≤ 1 - c := by linarith
  positivity

lemma Q_eval_zero_rec (k : ℕ) : eval 0 (Q (k+2)) = - (4*(k+2:ℝ)-2)*(k+2) * eval 0 (Q (k+1)) + (k+2)*(k+1) * eval 0 (Q k) := by
  have H : Q (k+2) = (- (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])) * Q (k+1) + ((k+2:ℝ[X])*(k+1:ℝ[X])) * Q k + E_poly (k+2) := by rfl
  rw [H, eval_add, eval_add, eval_mul, eval_mul]
  have hE := E_eval_zero k
  rw [hE, add_zero]
  simp

lemma Q_eval_one_rec (k : ℕ) : eval 1 (Q (k+2)) = - (4*(k+2:ℝ)-2)*(k+2) * eval 1 (Q (k+1)) + (k+2)*(k+1) * eval 1 (Q k) := by
  have H : Q (k+2) = (- (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])) * Q (k+1) + ((k+2:ℝ[X])*(k+1:ℝ[X])) * Q k + E_poly (k+2) := by rfl
  rw [H, eval_add, eval_add, eval_mul, eval_mul]
  have hE := E_eval_one k
  rw [hE, add_zero]
  simp
