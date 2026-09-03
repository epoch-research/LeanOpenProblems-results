import FormalConjecturesUtil

/-!
An exact boundary obstruction for a proposed rational-comparison
construction. This is not a proof or disproof of the original conjecture.
-/

namespace ShiftedMultiplierBoundary

/-- Starting at an exact reciprocal row, positivity forces the next shifted
multiplier to be strictly larger. -/
theorem positive_step_multiplier_gt (A q Q : ℕ)
    (hA : 2 ≤ A) (hq : 2 ≤ q) (hQ : 2 ≤ Q)
    (h : (0 : ℚ) < 1 / ((q : ℚ) * A - 1) - 1 / ((Q : ℚ) * A - 1)) :
    q < Q := by
  have ha : (2 : ℚ) ≤ A := by exact_mod_cast hA
  have hb : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hc : (2 : ℚ) ≤ Q := by exact_mod_cast hQ
  have hdq : (0 : ℚ) < (q : ℚ) * A - 1 := by nlinarith
  have hdQ : (0 : ℚ) < (Q : ℚ) * A - 1 := by nlinarith
  have hh : (1 : ℚ) / ((Q : ℚ) * A - 1) < 1 / ((q : ℚ) * A - 1) := by
    linarith
  have hm := (div_lt_div_iff₀ hdQ hdq).mp hh
  by_contra hn
  have hle : (Q : ℚ) ≤ q := by exact_mod_cast (Nat.le_of_not_gt hn)
  have hp := mul_le_mul_of_nonneg_right hle (by linarith : (0 : ℚ) ≤ A)
  nlinarith

/-- Even the least admissible larger multiplier leaves a scaled remainder
strictly above 1/q. Consequently a shrinking interval with upper endpoint
at most 1/q cannot contain this next state. -/
theorem scaled_step_gt_inverse (A q Q : ℕ)
    (hA : 2 ≤ A) (hq : 2 ≤ q) (hQq : q < Q) :
    (1 : ℚ) / q < (Q : ℚ) * A *
      (1 / ((q : ℚ) * A - 1) - 1 / ((Q : ℚ) * A - 1)) := by
  have ha : (2 : ℚ) ≤ A := by exact_mod_cast hA
  have hb : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hc : (q : ℚ) + 1 ≤ Q := by exact_mod_cast hQq
  have hq0 : (0 : ℚ) < q := by linarith
  have hdq : (0 : ℚ) < (q : ℚ) * A - 1 := by nlinarith
  have hdQ : (0 : ℚ) < (Q : ℚ) * A - 1 := by nlinarith
  have hp : (0 : ℚ) ≤ (q : ℚ) * Q * ((Q : ℚ) - q - 1) * (A : ℚ)^2 := by
    apply mul_nonneg
    · apply mul_nonneg (by positivity)
      linarith
    · exact sq_nonneg _
  have hid : (Q : ℚ) * A *
      (1 / ((q : ℚ) * A - 1) - 1 / ((Q : ℚ) * A - 1)) - 1 / q =
      ((q : ℚ) * Q * ((Q : ℚ) - q - 1) * (A : ℚ)^2 +
        ((q : ℚ) + Q) * A - 1) /
        ((q : ℚ) * ((q : ℚ) * A - 1) * ((Q : ℚ) * A - 1)) := by
    have hnq : (-1 + (A : ℚ) * q) ≠ 0 := by nlinarith
    have hnQ : (-1 + (A : ℚ) * Q) ≠ 0 := by nlinarith
    field_simp [hq0.ne', hdq.ne', hdQ.ne']
    ring_nf
    field_simp [hnq, hnQ]
    ring
  apply sub_pos.mp
  rw [hid]
  apply div_pos _ (mul_pos (mul_pos hq0 hdq) hdQ)
  have hx : (1 : ℚ) < ((q : ℚ) + Q) * A := by nlinarith
  linarith

/-- No positive step from an exact reciprocal row reaches the stated
smaller normalized interval. -/
theorem no_positive_small_step (A q Q : ℕ)
    (hA : 2 ≤ A) (hq : 2 ≤ q) (hQ : 2 ≤ Q) :
    ¬ ((0 : ℚ) < 1 / ((q : ℚ) * A - 1) - 1 / ((Q : ℚ) * A - 1) ∧
      (Q : ℚ) * A * (1 / ((q : ℚ) * A - 1) - 1 / ((Q : ℚ) * A - 1)) ≤
        1 / q) := by
  rintro ⟨hp, hs⟩
  exact (not_lt_of_ge hs) (scaled_step_gt_inverse A q Q hA hq
    (positive_step_multiplier_gt A q Q hA hq hQ hp))

end ShiftedMultiplierBoundary

#print axioms ShiftedMultiplierBoundary.positive_step_multiplier_gt
#print axioms ShiftedMultiplierBoundary.scaled_step_gt_inverse
#print axioms ShiftedMultiplierBoundary.no_positive_small_step
