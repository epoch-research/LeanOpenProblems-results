import Submission.SoftExposureLowTail
import Submission.HardCubicRectangularCriterion
import Submission.StretchedQuadraticVoid

/-! An unconditional lower-tail estimate at a fixed multiple of quadratic
length. The exponent is 4/5, still smaller than the full phase entropy.
This does not settle the quadratic Jacobsthal conjecture. -/
namespace Erdos970.SoftExposure
open Finset Real GapAverages FiniteSelberg Filter

lemma hardCubic_partial_count (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m t : ℕ) (ht : 0 < t)
    (hm : 2048 * hardCubicBoundConstant * (t : ℝ) ^ 160 ≤ m) (r : ℕ → ℕ) :
    PartialLower (2 * t ^ 64) (range m) P r
      ((m : ℝ) / hardCubicCountDenominator (2 * t ^ 16)) := by
  intro Q hQP hQcard
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp => hP p (hQP hp)
  have hcard : Q.card ≤ (2 * t ^ 16) ^ 4 := by
    have he : (2 * t ^ 16) ^ 4 = 16 * t ^ 64 := by ring
    rw [he]
    omega
  have hscale : 2 * hardCubicBoundConstant * ((2 * t ^ 16 : ℕ) : ℝ) ^ 10 ≤ m := by
    convert hm using 1 <;> push_cast <;> ring
  have hc := prime_count_three_quarters Q hQ (2 * t ^ 16) (by positivity) hcard r m hscale
  apply (div_le_iff₀ (hardCubicCountDenominator_pos _ (by positivity))).mpr
  simpa only [hardCubicCountDenominator, survivors, mul_comm] using hc

lemma soft_exposure_core_cost (D t b : ℕ) (ht : 0 < t)
    (hDt : 2048 * (D + 1) ≤ t) (hb : b ≤ D * t ^ 50 + 1) :
    (b : ℝ) * log (1 + 4 * (t : ℝ) ^ 64) ≤ (t : ℝ) ^ 64 / 32 := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have h50 : (1 : ℝ) ≤ (t : ℝ) ^ 50 := one_le_pow₀ ht1
  have h64 : (1 : ℝ) ≤ (t : ℝ) ^ 64 := one_le_pow₀ ht1
  have hlog0 : 0 ≤ log (1 + 4 * (t : ℝ) ^ 64) := log_nonneg (by have := pow_nonneg ht0.le 64; linarith)
  have hlog : log (1 + 4 * (t : ℝ) ^ 64) ≤ 64 * t := by
    have hh := log_le_log (by positivity : 0 < 1 + 4 * (t : ℝ) ^ 64)
      (show 1 + 4 * (t : ℝ) ^ 64 ≤ 5 * (t : ℝ) ^ 64 by nlinarith only [h64])
    rw [log_mul (by norm_num) (pow_ne_zero _ ht0.ne'), log_pow] at hh
    have h5 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    have hT := log_le_sub_one_of_pos ht0
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh, h5, hT]
  have hbR : (b : ℝ) ≤ ((D : ℝ) + 1) * (t : ℝ) ^ 50 := by
    have hh : (b : ℝ) ≤ (D : ℝ) * (t : ℝ) ^ 50 + 1 := by exact_mod_cast hb
    nlinarith only [hh, h50]
  have hDtR : 2048 * ((D : ℝ) + 1) ≤ t := by exact_mod_cast hDt
  have hp52 : (t : ℝ) ^ 52 ≤ (t : ℝ) ^ 64 := pow_le_pow_right₀ ht1 (by omega)
  have hh := mul_le_mul_of_nonneg_right hDtR (pow_nonneg ht0.le 51)
  have hc := mul_le_mul hbR hlog hlog0 (by positivity)
  nlinarith only [hh, hc, hp52]

/-- A quantitative sub-mean tail on an eightieth-power cardinality envelope.
Every ingredient is unconditional, including the partial-count input. -/
theorem lowCountFraction_envelope (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m t D : ℕ) (ht : 0 < t) (hcard : P.card ≤ t ^ 80)
    (hD1024 : 1024 ≤ D)
    (hlogD : 2048 * (WeightedMertens.boundConstant + 1) ≤ log (D : ℝ))
    (hDt : 2048 * (D + 1) ≤ t)
    (hm : 2048 * hardCubicBoundConstant * (t : ℝ) ^ 160 ≤ m)
    (hmpos : 0 < m) (b : ℝ) (hb : 0 ≤ b)
    (hbA : b ≤ (m : ℝ) / hardCubicCountDenominator (2 * t ^ 16) / 256) :
    lowCountFraction P m b ≤ exp (-(t : ℝ) ^ 64 / 64) := by
  let S := P.filter (fun p => p ≤ D * t ^ 50)
  have hSP : S ⊆ P := filter_subset _ _
  have hScard : S.card ≤ D * t ^ 50 + 1 := by
    have hs : S ⊆ range (D * t ^ 50 + 1) := by
      intro p hp
      exact mem_range.mpr (by have := (mem_filter.mp hp).2; omega)
    simpa only [card_range] using card_le_card hs
  have hhalf : (∑ p ∈ P \ S, (p : ℝ)⁻¹) ≤ 1 / 2 := by
    have he : P \ S = P.filter (fun p => D * t ^ 50 < p) := by
      ext p
      simp only [S, Finset.mem_sdiff, mem_filter]
      by_cases hp : p ∈ P <;> simp only [hp, true_and, false_and, not_true_eq_false, not_false_eq_true, not_le]
    rw [he]
    have hh := WeightedMertens.tail_five_eighths P hP (t ^ 5) D (by positivity) hD1024 hlogD
      (by simpa only [← pow_mul] using hcard)
    simpa only [← pow_mul, one_div] using hh
  have hA : 0 < (m : ℝ) / hardCubicCountDenominator (2 * t ^ 16) :=
    div_pos (by exact_mod_cast hmpos) (hardCubicCountDenominator_pos _ (by positivity))
  have hh := lowCountFraction_le_core_exponential P S hP hSP m (t ^ 64) (by positivity)
    ((m : ℝ) / hardCubicCountDenominator (2 * t ^ 16)) b hA hb hbA
    (fun r => hardCubic_partial_count P hP m t ht hm (phaseResidues P r)) hhalf
  have hc := soft_exposure_core_cost D t S.card ht hDt hScard
  apply hh.trans
  apply exp_le_exp.mpr
  push_cast
  linarith only [hc]

#print axioms hardCubic_partial_count
#print axioms lowCountFraction_envelope
end Erdos970.SoftExposure
