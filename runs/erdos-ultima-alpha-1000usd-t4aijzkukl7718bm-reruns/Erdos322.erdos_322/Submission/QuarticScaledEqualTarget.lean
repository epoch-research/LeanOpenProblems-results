import Submission.QuarticEqualTargetObstruction

/-! A fixed positive target factor does not circumvent the multilinear
quartic composition obstruction. This is not a representation-count bound. -/
namespace Erdos322Research.QuarticScaledEqualTarget

/-- Even with an arbitrary fixed positive multiplier, four equal-target
representations cannot be combined by a four-output multilinear norm formula. -/
theorem no_scaled_four_input_equal_target_formula
    (F : MultilinearMap ℝ (fun _ : Fin 4 ↦ Fin 4 → ℝ) (Fin 4 → ℝ))
    (C : ℝ) (hC : 0 < C) :
    ¬ (∀ (x : Fin 4 → Fin 4 → ℝ) (n : ℝ),
      (∀ j, ∑ i, x j i^4 = n) → ∑ i, F x i^4 = C*n^4) := by
  intro h
  let a := Real.sqrt (Real.sqrt C)
  have ha : 0 < a := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hC)
  have ha4 : a^4 = C := by
    dsimp only [a]
    calc
      (Real.sqrt (Real.sqrt C))^4 = ((Real.sqrt (Real.sqrt C))^2)^2 := by ring
      _ = C := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hC.le]
  let G : MultilinearMap ℝ (fun _ : Fin 4 ↦ Fin 4 → ℝ) (Fin 4 → ℝ) := a⁻¹ • F
  apply QuarticEqualTarget.no_four_input_equal_target_formula G
  intro x n hx
  change ∑ i, (a⁻¹*F x i)^4 = n^4
  simp only [mul_pow, ← Finset.mul_sum]
  rw [h x n hx, inv_pow, ha4]
  field_simp

end Erdos322Research.QuarticScaledEqualTarget
