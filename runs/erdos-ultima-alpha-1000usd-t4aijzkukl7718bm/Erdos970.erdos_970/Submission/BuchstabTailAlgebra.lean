import Submission.BuchstabTailMoments

/-! A common finite calculation for truncating seventh-moment tails at L/13.
The Euler upper coefficient, main coefficient, and sixth-moment error are all
kept explicit. It is used for both the upper-source and lower-deficit tails. -/
namespace Erdos970.FiniteSelberg
open Real

noncomputable def truncatedTailMain (B : ℝ) : ℝ := 9*B/(35*13^7)
noncomputable def truncatedTailError (B : ℝ) : ℝ :=
  18*B*WeightedMertens.sharpMomentError/(5*13^6)
noncomputable def initialGridTail : ℝ := (3/50)*8^8/(7*12^7)
noncomputable def lowerGridTail : ℝ := (3/2)*(4/525)*9^8/(7*12^7)
noncomputable def initialTailCoefficient : ℝ := 6*(26/3 : ℝ)^8/217
noncomputable def lowerTailCoefficient : ℝ := (2/3)*(4/525)*(39/4 : ℝ)^8

lemma initialGridTail_pos : 0 < initialGridTail := by norm_num [initialGridTail]
lemma lowerGridTail_pos : 0 < lowerGridTail := by norm_num [lowerGridTail]
lemma initialTailCoefficient_nonneg : 0 ≤ initialTailCoefficient := by norm_num [initialTailCoefficient]
lemma lowerTailCoefficient_nonneg : 0 ≤ lowerTailCoefficient := by norm_num [lowerTailCoefficient]

lemma initial_tail_main_budget : truncatedTailMain initialTailCoefficient ≤ (19/20)*initialGridTail := by
  norm_num [truncatedTailMain, initialTailCoefficient, initialGridTail]
lemma lower_tail_main_budget : truncatedTailMain lowerTailCoefficient ≤ (19/20)*lowerGridTail := by
  norm_num [truncatedTailMain, lowerTailCoefficient, lowerGridTail]

lemma truncatedTailError_nonneg (B : ℝ) (hB : 0 ≤ B) : 0 ≤ truncatedTailError B := by
  have hh := WeightedMertens.sharpMomentError_pos
  unfold truncatedTailError
  positivity

/-- All explicit error terms are absorbed by one threshold independent of s>=1. -/
theorem normalized_truncated_moment_le (S E L s R B T : ℝ)
    (hS : S ≤ (B/(s*L)^8)*(R^7/7+2*WeightedMertens.sharpMomentError*R^6))
    (hE : 0 ≤ E) (hEu : E ≤ (9/5)*L) (hL : 0 < L) (hs : 1 ≤ s)
    (hR : 0 ≤ R) (hRL : 13*R ≤ s*L) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hmain : truncatedTailMain B ≤ (19/20)*T)
    (hlarge : 20*truncatedTailError B ≤ T*L) : E*S ≤ T/s := by
  have hs0 : 0 < s := by linarith
  have hτ : 0 < s*L := mul_pos hs0 hL
  have hRe : R ≤ (s*L)/13 := by linarith
  have h7 := pow_le_pow_left₀ hR hRe 7
  have h6 := pow_le_pow_left₀ hR hRe 6
  have herr0 := WeightedMertens.sharpMomentError_pos
  have hmoment : R^7/7+2*WeightedMertens.sharpMomentError*R^6 ≤
      ((s*L)/13)^7/7+2*WeightedMertens.sharpMomentError*((s*L)/13)^6 := by
    exact add_le_add (div_le_div_of_nonneg_right h7 (by norm_num))
      (mul_le_mul_of_nonneg_left h6 (by positivity))
  let V := (B/(s*L)^8)*(((s*L)/13)^7/7+2*WeightedMertens.sharpMomentError*((s*L)/13)^6)
  have hSV : S ≤ V := hS.trans (mul_le_mul_of_nonneg_left hmoment (by positivity))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have halg : ((9/5)*L)*V = truncatedTailMain B/s+truncatedTailError B/(s^2*L) := by
    dsimp [V,truncatedTailMain,truncatedTailError]
    field_simp
    <;> ring
  have hbound : E*S ≤ truncatedTailMain B/s+truncatedTailError B/(s^2*L) := by
    calc
      E*S ≤ E*V := mul_le_mul_of_nonneg_left hSV hE
      _ ≤ ((9/5)*L)*V := mul_le_mul_of_nonneg_right hEu hV
      _ = _ := halg
  have hLτ : T*L ≤ T*(s*L) :=
    mul_le_mul_of_nonneg_left (by nlinarith : L ≤ s*L) hT
  have he : truncatedTailError B/(s*L) ≤ T/20 := by
    apply (div_le_iff₀ hτ).mpr
    linarith only [hlarge,hLτ]
  have he' : truncatedTailError B/(s^2*L) ≤ T/(20*s) := by
    have hh := div_le_div_of_nonneg_right he hs0.le
    convert hh using 1 <;> ring
  have hm := div_le_div_of_nonneg_right hmain hs0.le
  calc
    E*S ≤ truncatedTailMain B/s+truncatedTailError B/(s^2*L) := hbound
    _ ≤ ((19/20)*T)/s+T/(20*s) := add_le_add hm he'
    _ = T/s := by ring

#print axioms initial_tail_main_budget
#print axioms lower_tail_main_budget
#print axioms normalized_truncated_moment_le
end Erdos970.FiniteSelberg
