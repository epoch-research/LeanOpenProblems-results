import Submission.FareyDenominatorBound

/-! A stronger finite denominator exclusion, not a proof of Erdős 68. -/

namespace Erdos68Development

lemma scaled_reciprocal_floor_bounds (B d : ℕ) (hd : 0 < d) :
    (B / d : ℕ) ≤ (B : ℝ) * (1 / (d : ℝ)) ∧
      (B : ℝ) * (1 / (d : ℝ)) < ((B / d : ℕ) : ℝ) + 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [mul_one_div]
  constructor
  · apply (le_div_iff₀ hdR).mpr
    exact_mod_cast Nat.div_mul_le_self B d
  · apply (div_lt_iff₀ hdR).mpr
    exact_mod_cast (show B < (B / d + 1) * d by
      simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ B hd)

lemma scaled_partial_sum_floor_bounds (B N : ℕ) :
    ((∑ k ∈ Finset.range N, B / denom k : ℕ) : ℝ) ≤
        (B : ℝ) * ∑ k ∈ Finset.range N, term k ∧
      (B : ℝ) * ∑ k ∈ Finset.range N, term k ≤
        ((∑ k ∈ Finset.range N, B / denom k : ℕ) : ℝ) + N := by
  have hb (k : ℕ) : ((B / denom k : ℕ) : ℝ) ≤ (B : ℝ) * term k ∧
      (B : ℝ) * term k < ((B / denom k : ℕ) : ℝ) + 1 := by
    have hf : 2 ≤ (k + 2).factorial := by exact_mod_cast factorial_ge_two k
    have hd : 0 < denom k := by unfold denom; omega
    simpa only [term_eq_inv_denom] using scaled_reciprocal_floor_bounds B (denom k) hd
  constructor
  · simpa only [Nat.cast_sum, Finset.mul_sum] using
      (Finset.sum_le_sum (s := Finset.range N) (fun k _ => (hb k).1))
  · have h := Finset.sum_le_sum (s := Finset.range N) (fun k _ => (hb k).2.le)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, Nat.cast_sum, Finset.mul_sum] using h


private def hugeScale : ℕ := 10^240
private def hugeFloorSum : ℕ := 1253498755699953471643360937905798940369232208332013417063834716640952482048987170890242377470682233718290900331818588978470431493238520572472995798396351537628709775745347962339086852452841422851031196795029131010174583971527076796701465367

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma huge_floor_sum :
    (∑ k ∈ Finset.range 140, hugeScale / denom k) = hugeFloorSum := by
  norm_num [hugeScale, hugeFloorSum, Finset.sum_range_succ, denom, Nat.factorial]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma huge_scaled_sum_bounds :
    (hugeFloorSum : ℝ) < (hugeScale : ℝ) * (∑' k : ℕ, term k) ∧
      (hugeScale : ℝ) * (∑' k : ℕ, term k) < (hugeFloorSum : ℝ) + 141 := by
  have hb : (0 : ℝ) < hugeScale := by norm_num [hugeScale]
  have hf := scaled_partial_sum_floor_bounds hugeScale 140
  rw [huge_floor_sum] at hf
  norm_num only [Nat.cast_ofNat] at hf
  have he := partial_sum_error 140
  have hpos := mul_pos hb he.1
  have hupper := mul_le_mul_of_nonneg_left he.2 hb.le
  have htail : (hugeScale : ℝ) * ((3 / 2 : ℝ) * term 140) < 1 := by
    norm_num [hugeScale, term, Nat.factorial]
  constructor <;> nlinarith [hf.1, hf.2]

set_option maxHeartbeats 0 in
lemma sum_huge_farey_bounds :
    (10138725400903802062574407225972041894082713545006564691876673898936930961782296902878686047469413801 / 8088341017332992634409744751350956797733241625161194915099719936012921744537133798241494755517477409 : ℝ) < (∑' k : ℕ, term k) ∧
      (∑' k : ℕ, term k) < 9859631185216180047326386929737639844990956716414109712487940870013216327875426272655152076901410806 / 7865688849216738017781803514903644114106774862081775569734428323655767175313915273498490023469790253 := by
  have hb : (0 : ℝ) < hugeScale := by norm_num [hugeScale]
  have h := huge_scaled_sum_bounds
  have hlo : (hugeFloorSum : ℝ) / hugeScale < (∑' k : ℕ, term k) :=
    (div_lt_iff₀ hb).mpr (by simpa only [mul_comm] using h.1)
  have hhi : (∑' k : ℕ, term k) < ((hugeFloorSum : ℝ) + 141) / hugeScale :=
    (lt_div_iff₀ hb).mpr (by simpa only [mul_comm] using h.2)
  constructor
  · apply lt_trans _ hlo
    norm_num [hugeScale, hugeFloorSum]
  · apply lt_trans hhi
    norm_num [hugeScale, hugeFloorSum]

/-- A finite exclusion only: this is not an irrationality theorem. -/
theorem rational_denominator_gt_ten_pow_hundred (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) :
    10^100 < q.den := by
  obtain ⟨hlo, hhi⟩ := sum_huge_farey_bounds
  rw [hq] at hlo hhi
  have h := denominator_ge_of_farey_bounds q
    10138725400903802062574407225972041894082713545006564691876673898936930961782296902878686047469413801 8088341017332992634409744751350956797733241625161194915099719936012921744537133798241494755517477409 9859631185216180047326386929737639844990956716414109712487940870013216327875426272655152076901410806 7865688849216738017781803514903644114106774862081775569734428323655767175313915273498490023469790253
    (by norm_num) (by norm_num) (by norm_num) hlo hhi
  have hb : (10^100 : ℤ) < 8088341017332992634409744751350956797733241625161194915099719936012921744537133798241494755517477409 + 7865688849216738017781803514903644114106774862081775569734428323655767175313915273498490023469790253 := by norm_num
  exact_mod_cast lt_of_lt_of_le hb h

end Erdos68Development

#print axioms Erdos68Development.huge_floor_sum
#print axioms Erdos68Development.sum_huge_farey_bounds
#print axioms Erdos68Development.rational_denominator_gt_ten_pow_hundred
