import Mathlib
open Polynomial Real Nat MeasureTheory intervalIntegral Asymptotics Filter Topology Set

noncomputable def P_poly (k : ℕ) : ℝ[X] :=
  (X * (1 - X)) ^ k * C ((k ! : ℝ)⁻¹)

noncomputable def g_poly (k : ℕ) : ℝ[X] :=
  ((X * (1 - X)) ^ k * (X ^ 2 + C (2 * (k : ℝ) + 1) * X - C ((k : ℝ) + 1))) * C (((k + 1)! : ℝ)⁻¹)

lemma deriv_U_k (k : ℕ) :
  derivative ((X * (1 - X) : ℝ[X]) ^ k) = C (k : ℝ) * (X * (1 - X)) ^ (k - 1) * (1 - C 2 * X) := by
  rw [derivative_pow]
  have : derivative (X * (1 - X) : ℝ[X]) = 1 - C 2 * X := by
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_one, map_ofNat]; ring
  rw [this]

lemma g_poly_derivative (k : ℕ) :
  derivative (g_poly k) =
    (C (k : ℝ) * (X * (1 - X)) ^ (k - 1) * (1 - C 2 * X) * (X ^ 2 + C (2 * (k : ℝ) + 1) * X - C ((k : ℝ) + 1)) +
    (X * (1 - X)) ^ k * (C 2 * X + C (2 * (k : ℝ) + 1))) * C (((k + 1)! : ℝ)⁻¹) := by
  dsimp [g_poly]; rw [derivative_mul, derivative_mul]
  have H1 : derivative ((X * (1 - X) : ℝ[X]) ^ k) = C (k : ℝ) * (X * (1 - X)) ^ (k - 1) * (1 - C 2 * X) := deriv_U_k k
  rw [H1]
  have H2 : derivative (X ^ 2 + C (2 * (k : ℝ) + 1) * X - C ((k : ℝ) + 1)) = C 2 * X + C (2 * (k : ℝ) + 1) := by
    simp [map_ofNat]; ring
  rw [H2]
  have H3 : derivative (C (((k + 1)! : ℝ)⁻¹)) = 0 := derivative_C
  rw [H3]; ring

lemma deriv_identity_helper (K : ℝ) (Y : ℝ[X]) :
  let U : ℝ[X] := X * (1 - X)
  C K * Y * (1 - C 2 * X) * (X ^ 2 + C (2 * K + 1) * X - C (K + 1)) +
  (U * Y) * (C 2 * X + C (2 * K + 1)) =
  U ^ 2 * Y + C ((4 * K + 2) * (K + 1)) * (U * Y) - C (K * (K + 1)) * Y +
  (U * Y) * (X ^ 2 + C (2 * K + 1) * X - C (K + 1)) := by
  intro U; dsimp [U]; simp only [map_ofNat, map_one, map_mul, map_add]; ring

lemma fact_cancel_1 (k : ℕ) : (k ! : ℝ)⁻¹ * ((k + 1)! : ℝ) = (k + 1 : ℝ) := by
  have : ((k + 1)! : ℝ) = (k + 1 : ℝ) * (k ! : ℝ) := by rw [Nat.factorial_succ]; push_cast; ring
  rw [this]; have h_pos : (k ! : ℝ) ≠ 0 := by positivity
  calc
    (k ! : ℝ)⁻¹ * ((k + 1 : ℝ) * (k ! : ℝ)) = (k + 1 : ℝ) * ((k ! : ℝ)⁻¹ * (k ! : ℝ)) := by ring
    _ = (k + 1 : ℝ) * 1 := by rw [inv_mul_cancel₀ h_pos]
    _ = (k + 1 : ℝ) := by ring

lemma fact_cancel_2 (k : ℕ) (hk : 1 ≤ k) : ((k - 1) ! : ℝ)⁻¹ * ((k + 1)! : ℝ) = (k : ℝ) * (k + 1 : ℝ) := by
  have h1 : k = k - 1 + 1 := by omega
  have : ((k + 1)! : ℝ) = (k + 1 : ℝ) * (k : ℝ) * ((k - 1) ! : ℝ) := by
    rw [Nat.factorial_succ]
    have h2 : k ! = k * (k - 1) ! := by nth_rw 1 [h1]; rw [Nat.factorial_succ]; congr 1; omega
    rw [h2]; push_cast; ring
  rw [this]; have h_pos : ((k - 1) ! : ℝ) ≠ 0 := by positivity
  calc
    ((k - 1) ! : ℝ)⁻¹ * ((k + 1 : ℝ) * (k : ℝ) * ((k - 1) ! : ℝ)) = ((k + 1 : ℝ) * (k : ℝ)) * (((k - 1) ! : ℝ)⁻¹ * ((k - 1) ! : ℝ)) := by ring
    _ = (k + 1 : ℝ) * (k : ℝ) * 1 := by rw [inv_mul_cancel₀ h_pos]
    _ = (k : ℝ) * (k + 1 : ℝ) := by ring

lemma P_poly_identity (k : ℕ) (hk : 1 ≤ k) :
  derivative (g_poly k) = P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1) + g_poly k := by
  have H : derivative (g_poly k) * C ((k + 1)! : ℝ) = (P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1) + g_poly k) * C ((k + 1)! : ℝ) := by
    rw [g_poly_derivative k]
    dsimp [P_poly, g_poly]
    have hk1 : (X * (1 - X) : ℝ[X]) ^ (k + 1) = (X * (1 - X)) ^ 2 * (X * (1 - X)) ^ (k - 1) := by rw [← pow_add]; congr 1; omega
    have hk2 : (X * (1 - X) : ℝ[X]) ^ k = (X * (1 - X)) * (X * (1 - X)) ^ (k - 1) := by
      have : k = 1 + (k - 1) := by omega
      nth_rw 1 [this]; rw [pow_add, pow_one]
    rw [hk1, hk2]
    have h_cancel1 : C ((k ! : ℝ)⁻¹) * C ((k + 1)! : ℝ) = C (k + 1 : ℝ) := by rw [← C_mul, fact_cancel_1 k]
    have h_cancel2 : C (((k - 1)! : ℝ)⁻¹) * C ((k + 1)! : ℝ) = C ((k : ℝ) * (k + 1 : ℝ)) := by rw [← C_mul, fact_cancel_2 k hk]
    have h_cancel_g : C (((k + 1)! : ℝ)⁻¹) * C ((k + 1)! : ℝ) = 1 := by
      rw [← C_mul]; have : ((k + 1)! : ℝ)⁻¹ * ((k + 1)! : ℝ) = 1 := inv_mul_cancel₀ (by positivity); rw [this, C_1]
    simp only [add_mul, sub_mul, mul_add, mul_sub, mul_assoc]
    rw [h_cancel1, h_cancel2, h_cancel_g]
    simp only [map_ofNat, map_one, map_mul, map_add, mul_one]
    generalize (X * (1 - X) : ℝ[X]) ^ (k - 1) = Y; ring
  calc
    derivative (g_poly k) = derivative (g_poly k) * C ((k + 1)! : ℝ) * C (((k + 1)! : ℝ)⁻¹) := by rw [mul_assoc, ← C_mul, mul_inv_cancel₀, C_1, mul_one]; positivity
    _ = (P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1) + g_poly k) * C ((k + 1)! : ℝ) * C (((k + 1)! : ℝ)⁻¹) := by rw [H]
    _ = P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1) + g_poly k := by rw [mul_assoc, ← C_mul, mul_inv_cancel₀, C_1, mul_one]; positivity
