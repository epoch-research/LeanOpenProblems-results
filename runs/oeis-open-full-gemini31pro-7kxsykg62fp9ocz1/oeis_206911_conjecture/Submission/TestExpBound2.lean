import Mathlib

open Real

lemma bound_add_helper (x y : ℝ) (hy : y * (1 + x) = x) :
    let A_minus_1 := y + y^2/2 + y^3/6 + y^4/24
    let B := 1 + x + x^2/2 + x^3/6 + 5/96 * x^4
    (A_minus_1 * B + 1 - B) * (2304 * (1+x)^4) = 85*x^8 + 292*x^7 + 580*x^6 + 504*x^5 + 168*x^4 := by
  intro A_minus_1 B
  have hy2 : y^2 * (1+x)^2 = x^2 := by
    calc y^2 * (1+x)^2 = (y * (1+x)) * (y * (1+x)) := by ring
    _ = x * x := by rw [hy]
    _ = x^2 := by ring
  have hy3 : y^3 * (1+x)^3 = x^3 := by
    calc y^3 * (1+x)^3 = (y * (1+x)) * (y * (1+x)) * (y * (1+x)) := by ring
    _ = x * x * x := by rw [hy]
    _ = x^3 := by ring
  have hy4 : y^4 * (1+x)^4 = x^4 := by
    calc y^4 * (1+x)^4 = (y * (1+x)) * (y * (1+x)) * (y * (1+x)) * (y * (1+x)) := by ring
    _ = x * x * x * x := by rw [hy]
    _ = x^4 := by ring
  have h_A : A_minus_1 * 24 * (1+x)^4 = 24 * x * (1+x)^3 + 12 * x^2 * (1+x)^2 + 4 * x^3 * (1+x) + x^4 := by
    calc
      A_minus_1 * 24 * (1+x)^4 = 24 * (y * (1+x) * (1+x)^3) + 12 * (y^2 * (1+x)^2 * (1+x)^2) + 4 * (y^3 * (1+x)^3 * (1+x)) + (y^4 * (1+x)^4) := by
        dsimp [A_minus_1]
        ring
      _ = 24 * (x * (1+x)^3) + 12 * (x^2 * (1+x)^2) + 4 * (x^3 * (1+x)) + x^4 := by rw [hy, hy2, hy3, hy4]
      _ = 24 * x * (1+x)^3 + 12 * x^2 * (1+x)^2 + 4 * x^3 * (1+x) + x^4 := by ring
  have h_full : (A_minus_1 * B + 1 - B) * (2304 * (1+x)^4) = (A_minus_1 * 24 * (1+x)^4) * (96 * B) + 2304 * (1+x)^4 * (1 - B) := by ring
  rw [h_full, h_A]
  dsimp [B]
  ring

