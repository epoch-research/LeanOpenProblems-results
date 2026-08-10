import FormalConjectures.Util.ProblemImports

open Nat

lemma helper_exponent (n e : ℕ) (hn : n ≥ 11) (he : e ≥ 3) :
    (n + 10).factorial - (n + 10).factorial / e ≥ (n + 10).factorial / 2 + (n + 8).factorial := by
  have h_div_e : (n + 10).factorial / e ≤ (n + 10).factorial / 3 := Nat.div_le_div_left he (by decide)
  have h_sub_le : (n + 10).factorial - (n + 10).factorial / e ≥ (n + 10).factorial - (n + 10).factorial / 3 := by omega
  have h_fac : (n + 10).factorial = (n + 10) * (n + 9) * (n + 8).factorial := by
    have h1 : (n + 10).factorial = (n + 10) * (n + 9).factorial := rfl
    have h2 : (n + 9).factorial = (n + 9) * (n + 8).factorial := rfl
    rw [h1, h2, mul_assoc]
  have h_sum_le : (n + 10).factorial / 2 + (n + 8).factorial + (n + 10).factorial / 3 ≤ (n + 10).factorial := by
    clear h_div_e h_sub_le
    rw [h_fac]
    clear h_fac
    have h_bound : (n + 10) * (n + 9) ≥ 420 := by
      have h1 : n + 10 ≥ 21 := by omega
      have h2 : n + 9 ≥ 20 := by omega
      exact Nat.mul_le_mul h1 h2
    have h_X_pos : (n + 8).factorial ≥ 1 := Nat.factorial_pos _
    generalize h_C : (n + 10) * (n + 9) = C
    generalize h_X : (n + 8).factorial = X
    rw [h_C] at h_bound
    rw [h_X] at h_X_pos
    generalize h_Z : C * X = Z
    apply Nat.le_of_mul_le_mul_left _ (by decide : 0 < 6)
    have h_div2 : 2 * (Z / 2) ≤ Z := Nat.mul_div_le _ _
    have h_div3 : 3 * (Z / 3) ≤ Z := Nat.mul_div_le _ _
    have h_6X : 6 * X ≤ Z := by
      rw [← h_Z]
      calc
        6 * X ≤ 420 * X := Nat.mul_le_mul_right X (by omega : 6 ≤ 420)
        _     ≤ C * X   := Nat.mul_le_mul_right X h_bound
    have h_alg : 6 * (Z / 2 + X + Z / 3) = 3 * (2 * (Z / 2)) + 6 * X + 2 * (3 * (Z / 3)) := by ring
    calc
      6 * (Z / 2 + X + Z / 3) = 3 * (2 * (Z / 2)) + 6 * X + 2 * (3 * (Z / 3)) := h_alg
      _ ≤ 3 * Z + 6 * X + 2 * Z := by omega
      _ ≤ 3 * Z + Z + 2 * Z := by omega
      _ = 6 * Z := by ring
  have h_trans : (n + 10).factorial / 2 + (n + 8).factorial ≤ (n + 10).factorial - (n + 10).factorial / 3 := by omega
  clear h_fac h_sum_le
  omega
