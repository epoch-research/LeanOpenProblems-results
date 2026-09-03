import FormalConjecturesUtil
import Submission.NormalizedPrimeFactorAntiConcentration
import Submission.PrimeDiscrepancy

/-! Uniform approximation of the signed largest-prime-factor comparison by
continuous clipped comparisons. The required cancellation of these continuous
comparisons is a hypothesis, not a proved arithmetic result. -/

namespace Erdos371NormalizedSignApproximation

open Finset Filter Erdos371NormalizedPrimeFactorStability
  Erdos371NormalizedPrimeFactorAntiConcentration
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def clip (δ x : ℝ) : ℝ := max (-1) (min 1 (x/δ))

lemma clip_bounds (δ x : ℝ) : -1 ≤ clip δ x ∧ clip δ x ≤ 1 := by
  unfold clip
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

lemma clip_eq_one {δ x : ℝ} (hδ : 0 < δ) (h : δ ≤ x) : clip δ x = 1 := by
  have hh : 1 ≤ x/δ := (le_div_iff₀ hδ).mpr (by simpa using h)
  simp [clip,min_eq_left hh]

lemma clip_eq_neg_one {δ x : ℝ} (hδ : 0 < δ) (h : x ≤ -δ) : clip δ x = -1 := by
  have hh : x/δ ≤ -1 := (div_le_iff₀ hδ).mpr (by simpa using h)
  have hh' : x/δ ≤ 1 := by linarith
  simp [clip,min_eq_right hh',max_eq_left hh]

lemma clip_neg (δ x : ℝ) : clip δ (-x) = -clip δ x := by
  unfold clip
  rw [neg_div]
  rcases le_total (x/δ) (-1) with h | h
  · rw [min_eq_right (show x/δ ≤ 1 by linarith),max_eq_left h,
      min_eq_left (show (1:ℝ) ≤ -(x/δ) by linarith)]
    norm_num
  · rcases le_total (x/δ) 1 with h' | h'
    · rw [min_eq_right h',max_eq_right h,
        min_eq_right (show -(x/δ) ≤ 1 by linarith),
        max_eq_right (show (-1:ℝ) ≤ -(x/δ) by linarith)]
    · rw [min_eq_left h',min_eq_right (show -(x/δ) ≤ 1 by linarith),
        max_eq_left (show -(x/δ) ≤ -1 by linarith)]
      norm_num

lemma clip_continuous (δ : ℝ) : Continuous (clip δ) := by
  exact continuous_const.max (continuous_const.min (continuous_id.div_const δ))

noncomputable def comparison (δ : ℝ) (n : ℕ) : ℝ :=
  clip δ (level (n+1)-level n)

noncomputable def meanError (δ : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, |(Erdos371PrimeDiscrepancy.sign n : ℝ)-comparison δ n|)/N

noncomputable def mean (δ : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, comparison δ n)/N

lemma pointwise_error_bound (δ : ℝ) (n : ℕ) :
    |(Erdos371PrimeDiscrepancy.sign n : ℝ)-comparison δ n| ≤ 2 := by
  have hh := clip_bounds δ (level (n+1)-level n)
  unfold comparison Erdos371PrimeDiscrepancy.sign
  split_ifs <;> norm_num only [Int.cast_one,Int.cast_neg] <;>
    apply abs_le.mpr <;> constructor <;> linarith

lemma comparison_eq_sign {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 3 ≤ n)
    (hfar : δ < |level (n+1)-level n|) :
    comparison δ n = (Erdos371PrimeDiscrepancy.sign n : ℝ) := by
  by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
  · have hl := (level_ascent_iff hn).mpr h
    rw [abs_of_pos (sub_pos.mpr hl)] at hfar
    simp only [comparison,clip_eq_one hδ hfar.le,
      Erdos371PrimeDiscrepancy.sign,h,if_pos,Int.cast_one]
  · have hl : level (n+1) ≤ level n := by
      by_contra hh
      exact h ((level_ascent_iff hn).mp (lt_of_not_ge hh))
    rw [abs_of_nonpos (sub_nonpos.mpr hl)] at hfar
    have hh : level (n+1)-level n ≤ -δ := by linarith
    simp [comparison,clip_eq_neg_one hδ hh,Erdos371PrimeDiscrepancy.sign,h]

lemma meanError_bound {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    meanError δ N ≤ 2*((nearInputs δ N).card:ℝ)/N+6/N := by
  have hp (n : ℕ) :
      |(Erdos371PrimeDiscrepancy.sign n:ℝ)-comparison δ n| ≤
        (if |level (n+1)-level n| ≤ δ then (2:ℝ) else 0)+
        (if n<3 then (2:ℝ) else 0) := by
    by_cases hn : n<3
    · rw [if_pos hn]
      split_ifs <;> have hh := pointwise_error_bound δ n <;> linarith
    · rw [if_neg hn,add_zero]
      by_cases hnear : |level (n+1)-level n| ≤ δ
      · rw [if_pos hnear]
        exact pointwise_error_bound δ n
      · rw [if_neg hnear,comparison_eq_sign hδ (by omega) (lt_of_not_ge hnear),
          sub_self,abs_zero]
  have hs := sum_le_sum (fun n (_ : n ∈ range N) => hp n)
  rw [sum_add_distrib,← sum_filter,← sum_filter] at hs
  simp only [sum_const,nsmul_eq_mul] at hs
  have hc : ((range N).filter (fun n => n<3)).card ≤ 3 := by
    apply (card_le_card (show (range N).filter (fun n => n<3) ⊆ range 3 from
      fun _ hn => mem_range.mpr (mem_filter.mp hn).2)).trans_eq
    exact card_range 3
  have hc' : (((range N).filter (fun n => n<3)).card:ℝ) ≤ 3 := by exact_mod_cast hc
  have hh : (∑ n ∈ range N, |(Erdos371PrimeDiscrepancy.sign n:ℝ)-comparison δ n|) ≤
      2*((nearInputs δ N).card:ℝ)+6 := by
    change _ ≤ 2*(((range N).filter (fun n => |level (n+1)-level n|≤δ)).card:ℝ)+6
    nlinarith
  exact (div_le_div_of_nonneg_right hh (Nat.cast_nonneg N)).trans_eq (by ring)

/-- Choose the clipping parameter first; the mean error is then small at all
sufficiently large counting ranges. -/
theorem approximation {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, meanError δ N < ε := by
  obtain ⟨δ,hδ,hh⟩ := normalized_nonconcentration (show 0<ε/4 by positivity)
  have hc : Tendsto (fun N : ℕ => (6:ℝ)/N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 6
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hh,hc.eventually_lt_const (show 0<ε/2 by positivity)] with N hN hcN
  have hb := meanError_bound hδ N
  have he : 2*((nearInputs δ N).card:ℝ)/N = 2*(((nearInputs δ N).card:ℝ)/N) := by ring
  rw [he] at hb
  linarith

lemma signed_mean_error (δ : ℝ) (N : ℕ) :
    |(Erdos371PrimeDiscrepancy.total N:ℝ)/N-mean δ N| ≤ meanError δ N := by
  have he : (Erdos371PrimeDiscrepancy.total N:ℝ) =
      ∑ n ∈ range N, (Erdos371PrimeDiscrepancy.sign n:ℝ) := by
    simp [Erdos371PrimeDiscrepancy.total]
  rw [mean,meanError,he,← sub_div,← sum_sub_distrib,abs_div]
  simp only [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)

/-- A sufficient continuous-correlation criterion. Its cancellation hypothesis
is NOT established in this file. -/
theorem density_half_of_clipped_cancellation
    (h : ∀ δ : ℝ, 0 < δ → Tendsto (mean δ) atTop (𝓝 0)) :
    {n | Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)}.HasDensity (1/2) := by
  rw [Erdos371PrimeDiscrepancy.density_half_iff_total_mean_zero,Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,herr⟩ := approximation (show 0<ε/2 by positivity)
  have hma : Tendsto (fun N => |mean δ N|) atTop (𝓝 0) := by
    simpa using (h δ hδ).abs
  have hm := hma.eventually_lt_const (show (0:ℝ)<ε/2 by positivity)
  filter_upwards [herr,hm] with N he hmN
  rw [Real.dist_eq,sub_zero]
  have hh := abs_add_le ((Erdos371PrimeDiscrepancy.total N:ℝ)/N-mean δ N) (mean δ N)
  have hb := signed_mean_error δ N
  simp only [sub_add_cancel] at hh
  simpa only [abs_zero] using (show |(Erdos371PrimeDiscrepancy.total N:ℝ)/N|<ε by linarith)

end Erdos371NormalizedSignApproximation

#print axioms Erdos371NormalizedSignApproximation.approximation
#print axioms Erdos371NormalizedSignApproximation.density_half_of_clipped_cancellation
