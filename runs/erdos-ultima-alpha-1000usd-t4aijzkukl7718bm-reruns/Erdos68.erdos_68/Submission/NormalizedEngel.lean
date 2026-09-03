import Submission.ModifiedEngel

/-!
# Normalizing the strict modified Engel rule

The multiplier becomes the ordinary strict Engel digit under this change of
variable. The remainder update does not become the ordinary Engel update.
This is auxiliary work, not a solution of Erdős 68.
-/

namespace Erdos68Development

noncomputable def normalizedEngelValue (A r : ℝ) : ℝ := A * r / (1 + r)

lemma normalizedEngelValue_pos {A r : ℝ} (hA : 0 < A) (hr : 0 < r) :
    0 < normalizedEngelValue A r := by
  unfold normalizedEngelValue
  positivity

lemma strictEngelRatio_normalized {A r : ℝ} (hA : 0 < A) (hr : 0 < r) :
    strictEngelRatio A r = ⌊1 / normalizedEngelValue A r⌋ + 1 := by
  unfold strictEngelRatio normalizedEngelValue
  congr 2
  have hp : 1 + r ≠ 0 := by positivity
  field_simp [hA.ne', hr.ne', hp]

private lemma normalized_update_algebra {A r q : ℝ}
    (hA : 0 < A) (hr : 0 < r) (hB : 1 < q * A)
    (hE : 0 < q * normalizedEngelValue A r - 1)
    (hr' : 0 < r - 1 / (q * A - 1)) :
    normalizedEngelValue (q * A) (r - 1 / (q * A - 1)) =
      (q * normalizedEngelValue A r - 1) /
        ((1 - 1 / (q * A)) ^ 2 +
          (q * normalizedEngelValue A r - 1) / (q * A) ^ 2) := by
  have hBp : 0 < q * A := by linarith
  have hBm : q * A - 1 ≠ 0 := by linarith
  have hrp : 1 + r ≠ 0 := by positivity
  have hq : q ≠ 0 := by
    intro h
    simp [h] at hBp
  have hrp' : 1 + (r - 1 / (q * A - 1)) ≠ 0 := by linarith
  have hD : 0 < (1 - 1 / (q * A)) ^ 2 +
      (q * normalizedEngelValue A r - 1) / (q * A) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (div_pos hE (sq_pos_of_pos hBp))
  apply (eq_div_iff hD.ne').mpr
  change (q * A * (r - 1 / (q * A - 1)) /
      (1 + (r - 1 / (q * A - 1)))) * _ = _
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hrp').mpr
  unfold normalizedEngelValue
  field_simp [hA.ne', hr.ne', hBp.ne', hBm, hrp, hq]
  ring

lemma strictEngelStep_normalized {A r : ℝ} (hA : 0 < A) (hr : 0 < r) :
    normalizedEngelValue (strictEngelStep (A, r)).1 (strictEngelStep (A, r)).2 =
      ((strictEngelRatio A r : ℝ) * normalizedEngelValue A r - 1) /
        ((1 - 1 / ((strictEngelRatio A r : ℝ) * A)) ^ 2 +
          ((strictEngelRatio A r : ℝ) * normalizedEngelValue A r - 1) /
            ((strictEngelRatio A r : ℝ) * A) ^ 2) := by
  have hy := normalizedEngelValue_pos hA hr
  have hq : 1 / normalizedEngelValue A r < (strictEngelRatio A r : ℝ) := by
    rw [strictEngelRatio_normalized hA hr]
    exact_mod_cast Int.lt_floor_add_one (1 / normalizedEngelValue A r)
  have hE : 0 < (strictEngelRatio A r : ℝ) * normalizedEngelValue A r - 1 := by
    have hh := (div_lt_iff₀ hy).mp hq
    linarith
  obtain ⟨hB, hr'⟩ := strictEngel_step_pos hA hr
  exact normalized_update_algebra hA hr (by linarith) hE hr'

/-- A rational example showing that the normalized update is not `q*y-1`.
The reduced numerator increases from 1 to 2 at this first step. -/
lemma normalized_rational_first_step :
    normalizedEngelValue 1 (1 / 4) = 1 / 5 ∧
      strictEngelRatio 1 (1 / 4) = 6 ∧
      normalizedEngelValue (strictEngelStep (1, 1 / 4)).1
        (strictEngelStep (1, 1 / 4)).2 = 2 / 7 ∧
      (6 * normalizedEngelValue 1 (1 / 4) - 1 : ℝ) = 1 / 5 := by
  norm_num [normalizedEngelValue, strictEngelStep, strictEngelRatio]

#print axioms strictEngelStep_normalized
#print axioms normalized_rational_first_step

end Erdos68Development
