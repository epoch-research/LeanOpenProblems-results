import Submission.ContinuousIntervalQuantumGain

/-! A real-argument gain estimate, including the cell where the natural-length
half-density estimate need not hold. This is not a uniform accumulated estimate. -/
namespace Erdos970.ContinuousInterval

lemma quantum_gain_constant_bounds :
    1 / 2 ≤ (4 - 2 * Real.sqrt 3 : ℝ) ∧ (4 - 2 * Real.sqrt 3 : ℝ) < 9 / 16 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> nlinarith

lemma quantum_gain_numerator_bound {d l s : ℝ}
    (hl : 0 ≤ l) (hls : l ≤ s) :
    (s - l) * (2 * d - s - l) ≤
      (4 - 2 * Real.sqrt 3) * d * (d + s - l) := by
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hid : ((s - l) - (Real.sqrt 3 - 1) * d) ^ 2 =
      (4 - 2 * Real.sqrt 3) * d * (d + s - l) - (s - l) * (2 * d - s + l) := by
    ring_nf
    rw [hs]
    ring
  have hprod := mul_nonneg (sub_nonneg.mpr hls) hl
  nlinarith [sq_nonneg ((s - l) - (Real.sqrt 3 - 1) * d)]

/-- The maximum of the strengthened line minus these two supporting bounds
is at most `(4 - 2*sqrt(3))*d`. -/
lemma quantum_gain_of_two_supports {d l s t y : ℝ}
    (hd : 0 < d) (hl : 0 ≤ l) (hls : l ≤ s) (hsd : s ≤ d)
    (hy₁ : l * (1 + t) ≤ y) (hy₂ : l + s - d + d * t ≤ y) :
    quantumFactor d (l - s) * s * (1 + t) - y ≤ (4 - 2 * Real.sqrt 3) * d := by
  let b := quantumFactor d (l - s) * s
  have hb := quantum_adjusted_slope_bounds hd hl hls hsd
  change l ≤ b ∧ b ≤ s ∧ b - l ≤ d / 2 at hb
  have hden : 0 < d + s - l := by linarith
  have hm : (d + s - l) * b = d * s := by
    dsimp [b, quantumFactor]
    have he : d + s - l = d - (l - s) := by ring
    rw [he]
    field_simp [ne_of_gt (show 0 < d - (l - s) by linarith)]
  have hE : (d + s - l) * (b - l) = (s - l) * (d - l) := by nlinarith
  have hc0 : 0 ≤ (4 - 2 * Real.sqrt 3) * d :=
    mul_nonneg (by linarith [quantum_gain_constant_bounds.1]) hd.le
  change b * (1 + t) - y ≤ _
  rcases eq_or_lt_of_le (hls.trans hsd) with heq | hld
  · have he : b = l := by linarith [hb.2.1]
    rw [he]
    linarith
  · have hw₁ := mul_nonneg (show 0 ≤ d - b by linarith [hb.2.1]) (sub_nonneg.mpr hy₁)
    have hw₂ := mul_nonneg (sub_nonneg.mpr hb.1) (sub_nonneg.mpr hy₂)
    have hw : (d - l) * (b * (1 + t) - y) ≤ (b - l) * (2 * d - s - l) := by
      nlinarith
    have hscaled : (d - l) * ((d + s - l) * (b * (1 + t) - y)) ≤
        (d - l) * ((s - l) * (2 * d - s - l)) := by
      calc
        _ = (d + s - l) * ((d - l) * (b * (1 + t) - y)) := by ring
        _ ≤ (d + s - l) * ((b - l) * (2 * d - s - l)) :=
          mul_le_mul_of_nonneg_left hw hden.le
        _ = ((d + s - l) * (b - l)) * (2 * d - s - l) := by ring
        _ = _ := by rw [hE]; ring
    have hmain := le_of_mul_le_mul_left hscaled (sub_pos.mpr hld)
    have hnum := quantum_gain_numerator_bound (d := d) hl hls
    exact le_of_mul_le_mul_left (show (d + s - l) * (b * (1 + t) - y) ≤ (d + s - l) * ((4 - 2 * Real.sqrt 3) * d) by nlinarith [hmain, hnum]) hden

/-- One integer-threshold refinement changes a real-argument value by at most
`(4 - 2*sqrt(3))*d`, which is less than `9*d/16`. The natural-length estimate
`d/2` is stronger but cannot simply be used on the intervening real cell. -/
theorem Regular.quantumPatch_real_gain {d : ℝ} {L U : ℝ → ℝ}
    (h : Regular d L U) (g : ℕ) (hd : 0 < d) (hg : 0 < g)
    (hz : L ((g - 1 : ℕ) : ℝ) = 0) (x : ℝ) :
    let F := ContinuousInterval.quantumPatch d g (quantumSlope L g) (quantumIntercept L g) L
    0 ≤ F x - L x ∧ F x - L x ≤ (4 - 2 * Real.sqrt 3) * d := by
  dsimp only
  let l := L (g : ℝ)
  let s := quantumSlope L g
  let e := quantumFactor d (l - s)
  have hl : 0 ≤ l := h.lower_nonneg _
  have hsl := h.quantumSlope_bounds g
  have ha := h.quantumIntercept_nonpos g hg hz
  have hls : l ≤ s := by change l - s ≤ 0 at ha; linarith
  have he := quantumFactor_bounds hd (show l - s ≤ 0 by linarith)
  change 0 < e ∧ e ≤ 1 at he
  have hden : 0 < d - (l - s) := by linarith
  have hehalf : 1 / 2 ≤ e := by
    dsimp [e, quantumFactor]
    apply (le_div_iff₀ hden).mpr
    linarith [hsl.2]
  have hc : 0 ≤ (4 - 2 * Real.sqrt 3) * d :=
    mul_nonneg (by linarith [quantum_gain_constant_bounds.1]) hd.le
  refine ⟨sub_nonneg.mpr (le_max_left _ _), ?_⟩
  apply sub_le_iff_le_add.mpr
  change max (L x) (e * s * (x - ((g : ℝ) - 1))) ≤ (4 - 2 * Real.sqrt 3) * d + L x
  apply max_le (by linarith)
  by_cases hout : x ≤ (g : ℝ) ∨ (g : ℝ) + 1 ≤ x
  · have hs := chord_le_outside h.lower_convex (g : ℝ) x
      (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) hout
    have hi := quantumFactor_identity hd (show l - s ≤ 0 by linarith)
    change e * (l - s) + (1 - e) * d = 0 at hi
    have hch : chord L g x = l + s * (x - g) := by
      dsimp [chord, l, s, quantumSlope]
      ring
    rw [hch] at hs
    have hw := mul_le_mul_of_nonneg_left hs he.1.le
    have hn := mul_nonneg (sub_nonneg.mpr he.2) (h.lower_nonneg x)
    have hh := mul_le_mul_of_nonneg_right quantum_gain_constant_bounds.1 hd.le
    have hhalf : (1 - e) * d ≤ d / 2 := by nlinarith
    nlinarith
  · have hx0 : (g : ℝ) ≤ x := by push_neg at hout; linarith
    have hx1 : x ≤ (g : ℝ) + 1 := by push_neg at hout; linarith
    have hcast : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ g by omega), Nat.cast_one]
    rw [hcast] at hz
    have hp := chord_le_outside h.lower_convex ((g : ℝ) - 1) x
      (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
      (Or.inr (by linarith : (g : ℝ) - 1 + 1 ≤ x))
    have hlip := h.lower_lip x ((g : ℝ) + 1) hx1
    have hy₁ : l * (1 + (x - g)) ≤ L x := by
      simp only [chord, hz, sub_add_cancel, sub_zero, zero_add] at hp
      dsimp [l]
      nlinarith
    have hy₂ : l + s - d + d * (x - g) ≤ L x := by
      dsimp [l, s, quantumSlope]
      linarith
    have hh := quantum_gain_of_two_supports hd hl hls hsl.2 hy₁ hy₂
    change e * s * (1 + (x - g)) - L x ≤ _ at hh
    nlinarith

#print axioms Regular.quantumPatch_real_gain
end Erdos970.ContinuousInterval
