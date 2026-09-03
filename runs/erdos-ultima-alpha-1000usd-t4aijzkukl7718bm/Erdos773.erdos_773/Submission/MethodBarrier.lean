import FormalConjecturesUtil

/-!
The limitation of the present uniform collision estimate.
This bounds the *lower-bound expression* supplied by that estimate;
it is not an upper bound on the maximum Sidon-subset cardinality.
-/

namespace Erdos773

lemma quartic_expression_le_one (x : ℝ) (hx : 0 ≤ x) : x - x ^ 4 ≤ 1 := by
  by_cases h : x ≤ 1
  · nlinarith [pow_nonneg hx 4]
  · have h1 : 1 ≤ x := by linarith
    have hpow : x ≤ x ^ 4 := by
      simpa using pow_le_pow_right₀ h1 (show 1 ≤ (4 : ℕ) by norm_num)
    linarith

lemma uniform_alteration_expression_bound (N p : ℝ) (hN : 0 ≤ N) (hp : 0 ≤ p) :
    p * N - N ^ 2 * p ^ 4 ≤ N ^ (2 / 3 : ℝ) := by
  let r := N ^ (1 / 3 : ℝ)
  have hr : 0 ≤ r := Real.rpow_nonneg hN _
  have hr3 : r ^ 3 = N := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast hN]
    norm_num
  have hr2 : r ^ 2 = N ^ (2 / 3 : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast hN]
    congr 1
    norm_num
  have h := mul_le_mul_of_nonneg_left
    (quartic_expression_le_one (p * r) (mul_nonneg hp hr)) (sq_nonneg r)
  have he : r ^ 2 * (p * r - (p * r) ^ 4) = p * N - N ^ 2 * p ^ 4 := by
    calc
      _ = p * r ^ 3 - (r ^ 3) ^ 2 * p ^ 4 := by ring
      _ = _ := by rw [hr3]
  rw [he, mul_one, hr2] at h
  exact h

lemma subpower_estimate_expression_bound (N p C₃ C₄ δ : ℝ)
    (hN : 1 ≤ N) (hp : 0 ≤ p) (hC₃ : 0 ≤ C₃) (hC₄ : 1 ≤ C₄) (hδ : 0 ≤ δ) :
    p * N - (C₃ * N ^ (1 + 2 * δ)) * p ^ 3 -
      (C₄ * N ^ (2 + 2 * δ)) * p ^ 4 ≤ N ^ (2 / 3 : ℝ) := by
  have hN0 : 0 ≤ N := by linarith
  have hpow : N ^ 2 ≤ N ^ (2 + 2 * δ) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hcoef : N ^ 2 ≤ C₄ * N ^ (2 + 2 * δ) := by
    calc
      _ ≤ N ^ (2 + 2 * δ) := hpow
      _ ≤ C₄ * N ^ (2 + 2 * δ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hC₄)
          (Real.rpow_nonneg hN0 (2 + 2 * δ))]
  have h4 := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hp 4)
  have h3 : 0 ≤ (C₃ * N ^ (1 + 2 * δ)) * p ^ 3 := by positivity
  have hmain := uniform_alteration_expression_bound N p hN0 hp
  linarith


/-- A conditional capacity bound for a restricted modular lifting method.
The hypotheses are numerical assumptions, not bounds on arbitrary Sidon sets. -/
lemma first_order_capacity_bound (N p M : ℝ)
    (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hcap : M ≤ p) (hvolume : M ^ 2 * p ≤ N ^ 2) :
    M ≤ N ^ (2 / 3 : ℝ) := by
  have hc : M ^ 3 ≤ N ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hcap (sq_nonneg M)
    nlinarith only [h, hvolume]
  have hr : (N ^ (2 / 3 : ℝ)) ^ 3 = N ^ 2 := by
    rw [← Real.rpow_mul_natCast hN]
    norm_num
  apply le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (Real.rpow_nonneg hN _)
  rwa [hr]

lemma first_order_capacity_bound_with_constants (N p M : ℝ)
    (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hcap : M ≤ 2 * p) (hvolume : M ^ 2 * p ≤ 4 * N ^ 2) :
    M ≤ 2 * N ^ (2 / 3 : ℝ) := by
  have hc : M ^ 3 ≤ 8 * N ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hcap (sq_nonneg M)
    nlinarith only [h, hvolume]
  have hr : (2 * N ^ (2 / 3 : ℝ)) ^ 3 = 8 * N ^ 2 := by
    rw [mul_pow, ← Real.rpow_mul_natCast hN]
    norm_num
  apply le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (by positivity)
  rwa [hr]

#print axioms first_order_capacity_bound
#print axioms first_order_capacity_bound_with_constants

#print axioms subpower_estimate_expression_bound

end Erdos773
