import Submission.CompositePairWindow
import Submission.SublinearCorrelationCriterion

/-!
A uniform necessary obstruction under finiteness, and a one-sided sufficient
criterion for the full two-scale pair minorant. The sufficient error estimate
is a hypothesis, not an asserted estimate for irrational slopes.
-/
namespace Erdos972FullPairWindowCriterion

open Filter
open scoped Topology
open Erdos972PrimePowerError Erdos972CorrelationVaughan Erdos972Topology
open Erdos972TwoScalePairMinorant Erdos972MixedSmoothMean
open Erdos972SublinearCorrelationCriterion

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The scalar mean approaches its limiting constant uniformly over the
entire shrinking validity window. This says nothing about the actual sum. -/
lemma window_uniform_mean_lower {α c : ℝ} (hα : 1 ≤ α) (hc : c < 32/63) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 0 < t →
      t * Real.log (floorMul α N) ≤ 1/4 → c < pairMean t := by
  have he := (tendsto_order.mp pairMean_tendsto).1 c hc
  obtain ⟨δ, hδ, hδmean⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  have hM : Tendsto (floorMul α) atTop atTop :=
    tendsto_atTop_mono (self_le_floorMul hα) tendsto_id
  have hlog : Tendsto (fun N : ℕ => Real.log (floorMul α N)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hM)
  have hlarge := hlog.eventually (eventually_gt_atTop ((1/4 : ℝ)/δ))
  filter_upwards [hlarge] with N hN
  intro t ht hw
  apply hδmean
  refine ⟨ht, ?_⟩
  have hlogpos : 0 < Real.log (floorMul α N) :=
    (div_pos (by norm_num : (0 : ℝ) < 1/4) hδ).trans hN
  have hdlog : (1/4 : ℝ) < δ * Real.log (floorMul α N) := by
    have hh := (div_lt_iff₀ hδ).mp hN
    nlinarith only [hh]
  nlinarith only [hw, hdlog, hlogpos]

/-- If there are only finitely many genuine prime pairs, then at every
sufficiently large cutoff ALL valid positive parameters have a one-sided
mean defect larger than c*N, for every c < 32/63. This is a bound on the
actual full sum, not on an upper error budget. -/
theorem finite_pairs_uniform_window_gap {α c : ℝ} (hα : 1 ≤ α)
    (hfin : (primeSet α).Finite) (hc : c < 32/63) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 0 < t →
      t * Real.log (floorMul α N) ≤ 1/4 →
      c * (N : ℝ) < (N : ℝ) * pairMean t - pairMinorantSum t α N := by
  let ε : ℝ := (32/63-c)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hcε : c+ε < 32/63 := by dsimp [ε]; linarith
  have hm := window_uniform_mean_lower hα hcε
  have hsmall := (tendsto_order.mp
    (finite_primeSet_correlation_tendsto_zero hα hfin)).2 ε hε
  filter_upwards [hm, hsmall, eventually_ge_atTop (1 : ℕ)] with N hm hs hN
  intro t ht hw
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsum := pairMinorantSum_le hα ht N hw
  have hsumε := (div_lt_iff₀ hNR).mp hs
  have hmean := mul_lt_mul_of_pos_right (hm t ht hw) hNR
  nlinarith only [hsum, hsumε, hmean]

/-- Only a one-sided error estimate with a fixed saving below 32/63 is
needed, on arbitrarily large valid scales. The estimate remains an explicit
hypothesis; the fixed-parameter mean theorem does not establish it. -/
theorem infinite_of_frequently_small_window_defect {α c : ℝ} (hα : 1 ≤ α)
    (hc : c < 32/63)
    (hgood : ∃ᶠ N : ℕ in atTop, ∃ t : ℝ, 0 < t ∧
      t * Real.log (floorMul α N) ≤ 1/4 ∧
      (N : ℝ) * pairMean t - pairMinorantSum t α N ≤ c * (N : ℝ)) :
    (primeSet α).Infinite := by
  intro hfin
  have hgap := finite_pairs_uniform_window_gap hα hfin hc
  obtain ⟨N, ⟨t, ht, hw, he⟩, hN⟩ := (hgood.and_eventually hgap).exists
  exact (not_le_of_gt (hN t ht hw)) he

/-- A usual absolute-error estimate is a stronger sufficient hypothesis. -/
theorem infinite_of_frequently_small_window_error {α c : ℝ} (hα : 1 ≤ α)
    (hc : c < 32/63)
    (hgood : ∃ᶠ N : ℕ in atTop, ∃ t : ℝ, 0 < t ∧
      t * Real.log (floorMul α N) ≤ 1/4 ∧
      |pairMinorantSum t α N - (N : ℝ) * pairMean t| ≤ c * (N : ℝ)) :
    (primeSet α).Infinite := by
  apply infinite_of_frequently_small_window_defect hα hc
  apply hgood.mono
  rintro N ⟨t, ht, hw, he⟩
  refine ⟨t, ht, hw, ?_⟩
  calc
    (N : ℝ) * pairMean t - pairMinorantSum t α N ≤
        |pairMinorantSum t α N - (N : ℝ) * pairMean t| := by
      simpa only [neg_sub] using neg_le_abs
        (pairMinorantSum t α N - (N : ℝ) * pairMean t)
    _ ≤ c * (N : ℝ) := he

/-- A single finite minorant certificate supplies a genuine prime pair
beyond B. No moving asymptotic is needed once this inequality is known. -/
theorem prime_pair_beyond_of_minorant {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t)
    {B N : ℕ} (hN : 1 ≤ N)
    (hw : t * Real.log (floorMul α N) ≤ 1/4)
    (hlarge : primePowerBudget α N + primeCorrelation α B < pairMinorantSum t α N) :
    ∃ p : ℕ, B < p ∧ p ≤ N ∧ p.Prime ∧ (floorMul α p).Prime := by
  exact prime_pair_beyond_of_correlation hα hN
    (hlarge.trans_le (pairMinorantSum_le hα ht N hw))

#print axioms window_uniform_mean_lower
#print axioms finite_pairs_uniform_window_gap
#print axioms infinite_of_frequently_small_window_defect
#print axioms infinite_of_frequently_small_window_error
#print axioms prime_pair_beyond_of_minorant

end Erdos972FullPairWindowCriterion
