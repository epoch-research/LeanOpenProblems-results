import Submission.ContinuousIntervalQuantum

/-! Localization and a sharp natural-length gain bound for one integer-threshold
refinement. These do not estimate accumulation through later sieve stages. -/
namespace Erdos970.ContinuousInterval

/-- Algebraic bounds on the slope of the new support. -/
lemma quantum_adjusted_slope_bounds {d l s : ℝ} (hd : 0 < d)
    (hl : 0 ≤ l) (hls : l ≤ s) (hsd : s ≤ d) :
    l ≤ quantumFactor d (l - s) * s ∧
      quantumFactor d (l - s) * s ≤ s ∧
      quantumFactor d (l - s) * s - l ≤ d / 2 := by
  have ha : l - s ≤ 0 := sub_nonpos.mpr hls
  have he := quantumFactor_bounds hd ha
  have hden : 0 < d - (l - s) := by linarith
  have hm : (d - (l - s)) * (quantumFactor d (l - s) * s) = d * s := by
    unfold quantumFactor
    field_simp
  have hlb : l ≤ quantumFactor d (l - s) * s := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hls) (sub_nonneg.mpr (hls.trans hsd))]
  have hbs : quantumFactor d (l - s) * s ≤ s := by
    nlinarith [mul_le_mul_of_nonneg_right he.2 (hl.trans hls)]
  refine ⟨hlb, hbs, ?_⟩
  have h1 := mul_nonneg hd.le (sub_nonneg.mpr hsd)
  have h2 := mul_nonneg hd.le hl
  have h3 := mul_nonneg hl (sub_nonneg.mpr hls)
  nlinarith

/-- Before the trigger's preceding natural length, the new line is nonpositive. -/
lemma quantumPatch_eq_left_of_le {d s a : ℝ} {L : ℝ → ℝ} (g : ℕ)
    (hd : 0 < d) (ha : a ≤ 0) (hs : 0 ≤ s) (hL : ∀ x, 0 ≤ L x)
    (x : ℝ) (hx : x ≤ (g : ℝ) - 1) : ContinuousInterval.quantumPatch d g s a L x = L x := by
  apply max_eq_left
  exact (mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (quantumFactor_bounds hd ha).1.le hs) (sub_nonpos.mpr hx)).trans (hL x)

/-- At natural lengths the largest gain is attained exactly at the trigger.
In particular a single refinement adds at most half the reference density.
This claim is deliberately restricted to natural arguments. -/
theorem Regular.quantumPatch_nat_gain {d : ℝ} {L U : ℝ → ℝ}
    (h : Regular d L U) (g : ℕ) (hd : 0 < d) (hg : 0 < g)
    (hz : L ((g - 1 : ℕ) : ℝ) = 0) (n : ℕ) :
    let F := ContinuousInterval.quantumPatch d g (quantumSlope L g) (quantumIntercept L g) L
    (0 ≤ F n - L n ∧ F n - L n ≤ F g - L g) ∧ F g - L g ≤ d / 2 := by
  dsimp only
  let l := L (g : ℝ)
  let s := quantumSlope L g
  let b := quantumFactor d (l - s) * s
  have hl : 0 ≤ l := h.lower_nonneg _
  have hsl := h.quantumSlope_bounds g
  have ha := h.quantumIntercept_nonpos g hg hz
  have hls : l ≤ s := by change l - s ≤ 0 at ha; linarith
  have hb := quantum_adjusted_slope_bounds hd hl hls hsl.2
  change l ≤ b ∧ b ≤ s ∧ b - l ≤ d / 2 at hb
  have hbg : ContinuousInterval.quantumPatch d g s (l - s) L g = b := by
    simp only [ContinuousInterval.quantumPatch, show (g : ℝ) - ((g : ℝ) - 1) = 1 by ring, mul_one]
    exact max_eq_right hb.1
  change (0 ≤ ContinuousInterval.quantumPatch d g s (l - s) L n - L n ∧
    ContinuousInterval.quantumPatch d g s (l - s) L n - L n ≤ ContinuousInterval.quantumPatch d g s (l - s) L g - l) ∧
    ContinuousInterval.quantumPatch d g s (l - s) L g - l ≤ d / 2
  rw [hbg]
  refine ⟨⟨sub_nonneg.mpr (le_max_left _ _), ?_⟩, hb.2.2⟩
  by_cases hng : n < g
  · have hn : (n : ℝ) ≤ (g : ℝ) - 1 := by
      have hh : (n : ℝ) + 1 ≤ g := by exact_mod_cast hng
      linarith
    rw [quantumPatch_eq_left_of_le g hd (sub_nonpos.mpr hls) hsl.1 h.lower_nonneg n hn]
    linarith [hb.1]
  · have hn : (g : ℝ) ≤ n := by exact_mod_cast (show g ≤ n by omega)
    have hc := quantum_support_nat h g n
    change s * ((n : ℝ) - ((g : ℝ) - 1)) + (l - s) ≤ L n at hc
    have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb.2.1) (sub_nonneg.mpr hn)
    apply sub_le_iff_le_add.mpr
    change max (L n) (b * ((n : ℝ) - ((g : ℝ) - 1))) ≤ b - l + L n
    exact max_le (by linarith [hb.1]) (by nlinarith)

/-- After the next cell, whenever the old chord is at least the integer threshold,
the refinement does nothing. This gives a real-argument cutoff as well. -/
theorem Regular.quantumPatch_eq_of_chord_ge {d : ℝ} {L U : ℝ → ℝ}
    (h : Regular d L U) (g : ℕ) (hd : 0 < d) (hg : 0 < g)
    (hz : L ((g - 1 : ℕ) : ℝ) = 0) (x : ℝ)
    (hx : (g : ℝ) + 1 ≤ x) (hc : d ≤ chord L g x) :
    ContinuousInterval.quantumPatch d g (quantumSlope L g) (quantumIntercept L g) L x = L x := by
  let s := quantumSlope L g
  let a := quantumIntercept L g
  let e := quantumFactor d a
  have ha : a ≤ 0 := h.quantumIntercept_nonpos g hg hz
  have he := quantumFactor_bounds hd ha
  have hi := quantumFactor_identity hd ha
  have hs : chord L g x ≤ L x := chord_le_outside h.lower_convex g x
    (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) (Or.inr hx)
  have hch : chord L g x = s * (x - ((g : ℝ) - 1)) + a := by
    dsimp [chord, s, a, quantumSlope, quantumIntercept]
    ring
  have hid : e * s * (x - ((g : ℝ) - 1)) = e * chord L g x + (1 - e) * d := by
    rw [hch]
    change e * a + (1 - e) * d = 0 at hi
    nlinarith
  apply max_eq_left
  change e * s * (x - ((g : ℝ) - 1)) ≤ L x
  rw [hid]
  have hm := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr he.2)
  nlinarith

#print axioms Regular.quantumPatch_nat_gain
#print axioms Regular.quantumPatch_eq_of_chord_ge
end Erdos970.ContinuousInterval
