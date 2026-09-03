import Submission.HardCubicLowCountTail

/-! An unconditional stretched-exponential lower tail for counts at a fixed
quadratic length. This controls counts below a small constant times m/log k,
but does not exclude a single exceptional phase. -/
namespace Erdos970.SoftExposure
open Finset Real GapAverages FiniteSelberg Filter

lemma exists_power_envelope (k e : ℕ) (hk : 0 < k) (he : 0 < e) :
    ∃ t : ℕ, 0 < t ∧ k ≤ t ^ e ∧ t ^ e ≤ 2 ^ e * k ∧ t ≤ k := by
  have hex : ∃ t : ℕ, k ≤ t ^ e := ⟨k, Nat.le_self_pow he.ne' k⟩
  let t := Nat.find hex
  have hkt : k ≤ t ^ e := Nat.find_spec hex
  have ht : 0 < t := by
    by_contra hn
    have heq : t = 0 := by omega
    simp only [heq, zero_pow he.ne'] at hkt
    omega
  refine ⟨t, ht, hkt, ?_, Nat.find_min' hex (Nat.le_self_pow he.ne' k)⟩
  by_cases ht1 : t = 1
  · rw [ht1, one_pow]
    exact (show 1 ≤ k from hk).trans (Nat.le_mul_of_pos_left k (by positivity))
  · have hpred : (t - 1) ^ e < k := by
      have hh := Nat.find_min hex (show t - 1 < t by omega)
      omega
    have hh := Nat.pow_le_pow_left (show t ≤ 2 * (t - 1) by omega) e
    rw [Nat.mul_pow] at hh
    exact hh.trans (Nat.mul_le_mul_left _ hpred.le)

noncomputable def softQuadraticScale : ℕ :=
  (⌈2048 * hardCubicBoundConstant⌉₊ + 1) * 2 ^ 160

lemma softQuadraticScale_pos : 0 < softQuadraticScale := by
  unfold softQuadraticScale
  positivity

noncomputable def softLowCountLogConstant : ℝ :=
  256 * 800000000 * (2 * log (hardCubicCutoffScale : ℝ) + 6 * log 2 + 48)

lemma softLowCountLogConstant_pos : 0 < softLowCountLogConstant := by
  have hlog := log_natCast_nonneg hardCubicCutoffScale
  have hlog2 : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  unfold softLowCountLogConstant
  positivity

lemma hardCubic_denominator_le_log (t k : ℕ) (ht : 0 < t) (htk : t ≤ k) :
    256 * hardCubicCountDenominator (2 * t ^ 16) ≤
      softLowCountLogConstant * log ((k : ℝ) + 2) := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hH0 : (0 : ℝ) < hardCubicCutoffScale := by
    have hh := hardCubicCutoffScale_ge
    exact_mod_cast (show 0 < hardCubicCutoffScale by omega)
  have hlH := log_natCast_nonneg hardCubicCutoffScale
  have hl2 : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  have hl2half : (1 / 2 : ℝ) ≤ log 2 := by
    have hh := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hhalf : (1 / 2 : ℝ) ≤ log ((k : ℝ) + 2) :=
    hl2half.trans (log_le_log (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith))
  have hltk : log (t : ℝ) ≤ log ((k : ℝ) + 2) := by
    apply log_le_log ht0
    have hh : (t : ℝ) ≤ k := by exact_mod_cast htk
    linarith only [hh]
  have he : hardCubicCountDenominator (2 * t ^ 16) =
      800000000 * (log (hardCubicCutoffScale : ℝ) + 3 * log 2 + 48 * log (t : ℝ)) := by
    unfold hardCubicCountDenominator
    push_cast
    rw [log_mul hH0.ne' (by positivity), log_pow, log_mul (by norm_num) (pow_ne_zero _ ht0.ne'), log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  have hh := mul_le_mul_of_nonneg_left hhalf
    (show 0 ≤ 2 * log (hardCubicCutoffScale : ℝ) + 6 * log 2 by positivity)
  rw [he, softLowCountLogConstant]
  nlinarith only [hh, hltk]

lemma softQuadraticScale_budget (k t : ℕ) (hroot : t ^ 80 ≤ 2 ^ 80 * k) :
    2048 * hardCubicBoundConstant * (t : ℝ) ^ 160 ≤ (softQuadraticScale * k ^ 2 : ℕ) := by
  have hscale : 2048 * hardCubicBoundConstant ≤ (⌈2048 * hardCubicBoundConstant⌉₊ + 1 : ℕ) := by
    have hh := Nat.le_ceil (2048 * hardCubicBoundConstant)
    push_cast
    linarith only [hh]
  have hpow : t ^ 160 ≤ 2 ^ 160 * k ^ 2 := by
    have hh := Nat.pow_le_pow_left hroot 2
    convert hh using 1 <;> ring
  calc
    _ ≤ (⌈2048 * hardCubicBoundConstant⌉₊ + 1 : ℕ) * (t : ℝ) ^ 160 :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    _ ≤ (⌈2048 * hardCubicBoundConstant⌉₊ + 1 : ℕ) * ((2 : ℝ) ^ 160 * (k : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hpow) (Nat.cast_nonneg _)
    _ = _ := by simp only [softQuadraticScale, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]; ring

lemma root_four_fifths (k t : ℕ) (hkt : k ≤ t ^ 80) :
    (k : ℝ) ^ ((4 : ℝ) / 5) ≤ (t : ℝ) ^ 64 := by
  have hh := rpow_le_rpow (Nat.cast_nonneg k)
    (show (k : ℝ) ≤ (t : ℝ) ^ 80 by exact_mod_cast hkt) (by norm_num : (0 : ℝ) ≤ 4 / 5)
  have he : ((t : ℝ) ^ 80) ^ ((4 : ℝ) / 5) = (t : ℝ) ^ 64 := by
    rw [← rpow_natCast (t : ℝ) 80, ← rpow_mul (Nat.cast_nonneg t)]
    norm_num
  rwa [he] at hh

/-- The new unconditional lower-tail estimate. Both the length scale and the
small-density constant are absolute, independent of the chosen prime set. -/
theorem eventually_soft_quadratic_low_tail :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      lowCountFraction P (softQuadraticScale * k ^ 2)
        ((softQuadraticScale * k ^ 2 : ℕ) / (softLowCountLogConstant * log ((k : ℝ) + 2))) ≤
          exp (-((k : ℝ) ^ ((4 : ℝ) / 5) / 64)) := by
  let D := thirteenSixteenthCutoffScale
  let T := 2048 * (D + 1)
  have hT : 0 < T := by dsimp [T]; positivity
  filter_upwards [eventually_ge_atTop (T ^ 80)] with k hk
  intro P hP hPk
  have hkpos : 0 < k := (Nat.pow_pos hT).trans_le hk
  obtain ⟨t, ht, hkt, hroot, htk⟩ := exists_power_envelope k 80 hkpos (by omega)
  have hTt : T ≤ t := (Nat.pow_le_pow_iff_left (by norm_num : (80 : ℕ) ≠ 0)).mp (hk.trans hkt)
  have hD1024 : 1024 ≤ D := (by norm_num : 1024 ≤ 65536).trans thirteenSixteenthCutoffScale_ge
  have hlogD : 2048 * (WeightedMertens.boundConstant + 1) ≤ log (D : ℝ) := exposureCutoffScale_log
  let m := softQuadraticScale * k ^ 2
  have hmpos : 0 < m := Nat.mul_pos softQuadraticScale_pos (Nat.pow_pos hkpos)
  have hb : 0 ≤ (m : ℝ) / (softLowCountLogConstant * log ((k : ℝ) + 2)) := by
    apply div_nonneg (Nat.cast_nonneg _)
    exact mul_nonneg softLowCountLogConstant_pos.le (log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k; linarith))
  have hdenpos : 0 < hardCubicCountDenominator (2 * t ^ 16) :=
    hardCubicCountDenominator_pos _ (by positivity)
  have hbA : (m : ℝ) / (softLowCountLogConstant * log ((k : ℝ) + 2)) ≤
      (m : ℝ) / hardCubicCountDenominator (2 * t ^ 16) / 256 := by
    have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg m)
      (show 0 < 256 * hardCubicCountDenominator (2 * t ^ 16) by positivity)
      (hardCubic_denominator_le_log t k ht htk)
    convert hh using 1
    ring
  have hh := lowCountFraction_envelope P hP m t D ht (hPk.trans hkt) hD1024 hlogD hTt
    (softQuadraticScale_budget k t hroot) hmpos _ hb hbA
  apply hh.trans
  apply exp_le_exp.mpr
  have he := root_four_fifths k t hkt
  linarith only [he]

/-- Existential form, without naming the large absolute constants. -/
theorem exists_soft_quadratic_low_tail :
    ∃ B : ℕ, 0 < B ∧ ∃ L > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
        lowCountFraction P (B * k ^ 2) ((B * k ^ 2 : ℕ) / (L * log ((k : ℝ) + 2))) ≤
          exp (-((k : ℝ) ^ ((4 : ℝ) / 5) / 64)) :=
  ⟨softQuadraticScale, softQuadraticScale_pos, softLowCountLogConstant,
    softLowCountLogConstant_pos, eventually_soft_quadratic_low_tail⟩

#print axioms eventually_soft_quadratic_low_tail
#print axioms exists_soft_quadratic_low_tail
end Erdos970.SoftExposure
