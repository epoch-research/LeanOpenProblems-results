import Mathlib
import Submission.Spec2_part2

lemma sqrt_bounds (k x : ℤ) (hk : 0 < k) (hx : 0 < x) (h1 : x^2 ≤ 2*k^2) (h2 : 2*k^2 < (x+1)^2) :
  (x - k : ℝ) ≤ (k : ℝ) * (Real.sqrt 2 - 1) ∧ (k : ℝ) * (Real.sqrt 2 - 1) < (x - k + 1 : ℝ) := by
  have hk_r : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hx_r : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have h1_r : (x : ℝ)^2 ≤ 2 * (k : ℝ)^2 := by exact_mod_cast h1
  have h2_r : 2 * (k : ℝ)^2 < (x + 1 : ℝ)^2 := by exact_mod_cast h2
  constructor
  · have h_le : (x : ℝ) ≤ Real.sqrt (2 * (k : ℝ)^2) := Real.le_sqrt_of_sq_le h1_r
    have h_sqrt_mul : Real.sqrt (2 * (k : ℝ)^2) = Real.sqrt 2 * (k : ℝ) := by
      rw [Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_sq hk_r]
    rw [h_sqrt_mul] at h_le
    calc (x - k : ℝ) = (x : ℝ) - (k : ℝ) := by ring
      _ ≤ Real.sqrt 2 * (k : ℝ) - (k : ℝ) := by linarith
      _ = (k : ℝ) * (Real.sqrt 2 - 1) := by ring
  · have h_lt : Real.sqrt (2 * (k : ℝ)^2) < Real.sqrt ((x + 1 : ℝ)^2) := by
      apply Real.sqrt_lt_sqrt (by positivity) h2_r
    have h_sqrt_mul : Real.sqrt (2 * (k : ℝ)^2) = Real.sqrt 2 * (k : ℝ) := by
      rw [Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_sq hk_r]
    rw [h_sqrt_mul] at h_lt
    have h_sqrt_sq : Real.sqrt ((x + 1 : ℝ)^2) = (x + 1 : ℝ) := Real.sqrt_sq (by positivity)
    rw [h_sqrt_sq] at h_lt
    calc (k : ℝ) * (Real.sqrt 2 - 1) = Real.sqrt 2 * (k : ℝ) - (k : ℝ) := by ring
      _ < (x + 1 : ℝ) - (k : ℝ) := by linarith
      _ = (x - k + 1 : ℝ) := by ring

lemma floor_eq (k x : ℤ) (hk : 0 < k) (hx : 0 < x) 
  (h1 : x^2 ≤ 2*k^2) (h2 : 2*k^2 < (x+1)^2) :
  Int.floor ((k : ℝ) * (Real.sqrt 2 - 1)) = x - k := by
  have h_b := sqrt_bounds k x hk hx h1 h2
  rw [Int.floor_eq_iff]
  push_cast
  exact h_b

noncomputable def b (k : ℕ) : ℤ :=
  let exponent_real : ℝ := (k : ℝ) * (Real.sqrt 2 - 1)
  let exponent_int : ℤ := Int.floor exponent_real
  (-1 : ℤ) ^ exponent_int.toNat

lemma b_eval (k : ℕ) (hk : 0 < k) (x : ℤ) (hx : 0 < x) 
  (h1 : x^2 ≤ 2*(k : ℤ)^2) (h2 : 2*(k : ℤ)^2 < (x+1)^2) :
  b k = (-1 : ℤ) ^ (x - (k : ℤ)).toNat := by
  unfold b
  dsimp only []
  have hk_int : 0 < (k : ℤ) := by exact_mod_cast hk
  have h_floor := floor_eq k x hk_int hx h1 h2
  push_cast at h_floor
  rw [h_floor]
