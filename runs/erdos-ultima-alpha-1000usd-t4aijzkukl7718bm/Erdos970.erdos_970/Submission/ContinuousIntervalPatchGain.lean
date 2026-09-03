import Submission.ContinuousIntervalInterpolation

/-! Quantitative gain from one batch of lattice interpolation. These estimates
do not bound the accumulation of improvements through later sieve stages and
do not settle uniform quadratic positivity. -/
namespace Erdos970.ContinuousInterval

lemma unit_cell_product_le_quarter (a x : ℝ) :
    (a + 1 - x) * (x - a) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (x - a - 1 / 2)]

lemma Regular.lower_chord_gain {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (a x : ℝ) : chord L a x ≤ L x + d / 4 := by
  by_cases hout : x ≤ a ∨ a + 1 ≤ x
  · have hh := chord_le_outside h.lower_convex a x
      (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) hout
    linarith [h.density_nonneg]
  · have hx0 : a ≤ x := by push_neg at hout; linarith
    have hx1 : x ≤ a + 1 := by push_neg at hout; linarith
    have hs : 0 ≤ a + 1 - x := by linarith
    have ht : 0 ≤ x - a := by linarith
    have hm := mul_le_mul_of_nonneg_left (h.lower_mono hx0) hs
    have hl := mul_le_mul_of_nonneg_left (h.lower_lip x (a + 1) hx1) ht
    have hlocal : chord L a x - L x ≤ d * ((a + 1 - x) * (x - a)) := by
      unfold chord
      nlinarith
    have hglobal := mul_le_mul_of_nonneg_left (unit_cell_product_le_quarter a x)
      h.density_nonneg
    linarith

def UpperLip (D : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → x ≤ y → U y - U x ≤ D * (y - x)

lemma Regular.density_le_upperLip {d D : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (hu : UpperLip D U) : d ≤ D := by
  have hh := h.upper_growth 0 1 (by norm_num) (by norm_num)
  have hh' := hu 0 1 (by norm_num) (by norm_num)
  linarith

lemma Regular.upper_chord_gain {d D : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (hu : UpperLip D U) (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    U x - (D - d) / 4 ≤ chord U a x := by
  have hdD : 0 ≤ D - d := sub_nonneg.mpr (h.density_le_upperLip hu)
  by_cases hout : x ≤ a ∨ a + 1 ≤ x
  · have hh := le_chord_outside h.upper_concave a x ha (by linarith : 0 ≤ a + 1) hx hout
    linarith
  · have hx0 : a ≤ x := by push_neg at hout; linarith
    have hx1 : x ≤ a + 1 := by push_neg at hout; linarith
    have hs : 0 ≤ a + 1 - x := by linarith
    have ht : 0 ≤ x - a := by linarith
    have hl := mul_le_mul_of_nonneg_left (hu a x ha hx0) hs
    have hg := mul_le_mul_of_nonneg_left (h.upper_growth x (a + 1) hx hx1) ht
    have hlocal : U x - chord U a x ≤ (D - d) * ((a + 1 - x) * (x - a)) := by
      unfold chord
      nlinarith
    have hglobal := mul_le_mul_of_nonneg_left (unit_cell_product_le_quarter a x) hdD
    linarith

lemma chordPatches_lower_le {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (cells : List ℕ) (x B : ℝ) (hL : L x ≤ B)
    (hC : ∀ a ∈ cells, chord L a x ≤ B) : (ContinuousInterval.chordPatches cells L U).1 x ≤ B := by
  induction cells generalizing L U with
  | nil => exact hL
  | cons a cells ih =>
    apply ih (h.patch a) (max_le hL (hC a List.mem_cons_self))
    intro b hb
    rw [chord_nat_congr (fun n => patchLower_nat h a n) b x]
    exact hC b (List.mem_cons_of_mem a hb)

lemma le_chordPatches_upper {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (cells : List ℕ) (x B : ℝ) (hU : B ≤ U x)
    (hC : ∀ a ∈ cells, B ≤ chord U a x) : B ≤ (ContinuousInterval.chordPatches cells L U).2 x := by
  induction cells generalizing L U with
  | nil => exact hU
  | cons a cells ih =>
    apply ih (h.patch a) (le_min hU (hC a List.mem_cons_self))
    intro b hb
    rw [chord_nat_congr (fun n => patchUpper_nat h a n) b x]
    exact hC b (List.mem_cons_of_mem a hb)

/-- The gain of a whole finite patch batch does not accumulate with its number
of cells: all patches preserve the same natural-length values. -/
theorem Regular.chordPatches_gain {d D : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (hu : UpperLip D U) (cells : List ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (0 ≤ (ContinuousInterval.chordPatches cells L U).1 x - L x ∧
      (ContinuousInterval.chordPatches cells L U).1 x - L x ≤ d / 4) ∧
    (0 ≤ U x - (ContinuousInterval.chordPatches cells L U).2 x ∧
      U x - (ContinuousInterval.chordPatches cells L U).2 x ≤ (D - d) / 4) := by
  have hd := chordPatches_dominates cells L U
  have hl := chordPatches_lower_le h cells x (L x + d / 4)
    (by linarith [h.density_nonneg]) (fun a _ => h.lower_chord_gain a x)
  have hu' := le_chordPatches_upper h cells x (U x - (D - d) / 4)
    (by linarith [h.density_le_upperLip hu])
    (fun a _ => h.upper_chord_gain hu a x (Nat.cast_nonneg a) hx)
  exact ⟨⟨sub_nonneg.mpr (hd.1 x), by linarith⟩,
    ⟨sub_nonneg.mpr (hd.2 x hx), by linarith⟩⟩

lemma UpperLip.patch {D : ℝ} {U : ℝ → ℝ} (h : UpperLip D U) (a : ℕ) :
    UpperLip D (patchUpper U a) := by
  intro x y hx hxy
  have hc : chord U a y - chord U a x ≤ D * (y - x) := by
    have ha := h a ((a : ℝ) + 1) (Nat.cast_nonneg a) (by linarith)
    simp only [add_sub_cancel_left, mul_one] at ha
    have hh := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hxy)
    unfold chord
    nlinarith
  dsimp only [patchUpper]
  by_cases he : U x ≤ chord U a x
  · rw [min_eq_left he]
    exact (sub_le_sub_right (min_le_left _ _) _).trans (h x y hx hxy)
  · rw [min_eq_right (le_of_not_ge he)]
    exact (sub_le_sub_right (min_le_right _ _) _).trans hc

lemma UpperLip.chordPatches {D : ℝ} {L U : ℝ → ℝ} (h : UpperLip D U)
    (cells : List ℕ) : UpperLip D (ContinuousInterval.chordPatches cells L U).2 := by
  induction cells generalizing L U with
  | nil => exact h
  | cons a cells ih => exact ih (h.patch a)

lemma UpperLip.step {d D Q : ℝ} {L U : ℝ → ℝ} (h : UpperLip D U)
    (hr : Regular d L U) (hQ : 0 ≤ Q) : UpperLip D (stepUpper Q L U) := by
  intro x y hx hxy
  have hh := h x y hx hxy
  have hm := hr.lower_mono (show (x + 1) * Q - 1 ≤ (y + 1) * Q - 1 by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hQ])
  unfold stepUpper
  linarith

/-- Every patched reference upper envelope has slope at most one. -/
theorem patchedEnvelope_upperLip (Q : ℕ → ℝ) (cells : ℕ → List ℕ) (k : ℕ)
    (hQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1) : UpperLip 1 (patchedEnvelope Q cells k).2 := by
  induction k with
  | zero => intro x y hx hxy; simp [patchedEnvelope]
  | succ k ih =>
    have hQQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1 := fun i hi => hQ i (by omega)
    exact ((ih hQQ).step (patchedEnvelope_regular Q cells k hQQ)
      (hQ k (by omega)).1).chordPatches (cells k)

#print axioms Regular.chordPatches_gain
#print axioms patchedEnvelope_upperLip
end Erdos970.ContinuousInterval
