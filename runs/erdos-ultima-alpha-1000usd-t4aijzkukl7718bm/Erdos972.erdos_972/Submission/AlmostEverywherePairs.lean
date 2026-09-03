import Submission.LocalTailMeasure

/-! Almost-everywhere prime-pair infinitude on an interior slope range. This
metric theorem does not settle the remaining pointwise exceptional slopes. -/
namespace Erdos972AlmostEverywherePairs

open MeasureTheory Filter Set
open scoped Topology ENNReal
open Erdos972LocalTailMeasure Erdos972Topology Erdos972RichSlopes

/-- A uniform positive relative measure in every subinterval forces a measurable
set to have full measure in the ambient interval, by Lebesgue differentiation. -/
theorem ae_mem_of_local_measure_lower {U : Set ℝ} (hU : MeasurableSet U)
    {A B κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ a b : ℝ, A < a → a < b → b < B →
      κ * (b - a) ≤ volume.real (Ioo a b ∩ U)) :
    ∀ᵐ x : ℝ, A < x → x < B → x ∈ U := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hU]
    with x hx
  intro hxA hxB
  by_contra hxU
  have hzero : U.indicator (1 : ℝ → ℝ≥0∞) x = 0 := Set.indicator_of_notMem hxU _
  rw [hzero] at hx
  have hr := (ENNReal.tendsto_toReal (show (0 : ℝ≥0∞) ≠ ⊤ by simp)).comp hx
  simp only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_zero] at hr
  change Tendsto (fun r => volume.real (U ∩ Metric.closedBall x r) /
    volume.real (Metric.closedBall x r)) (𝓝[>] 0) (𝓝 0) at hr
  have hl : ∀ᶠ r in 𝓝[>] (0 : ℝ), κ ≤ volume.real (U ∩ Metric.closedBall x r) /
      volume.real (Metric.closedBall x r) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (sub_pos.mpr hxA)).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds (sub_pos.mpr hxB)).filter_mono nhdsWithin_le_nhds]
      with r hr0 hra hrb
    change 0 < r at hr0
    have ha : A < x - r := by linarith
    have hb : x + r < B := by linarith
    have hm := hlower (x - r) (x + r) ha (by linarith) hb
    have hsub : Ioo (x - r) (x + r) ∩ U ⊆ U ∩ Metric.closedBall x r := by
      intro y hy
      rw [Real.closedBall_eq_Icc]
      exact ⟨hy.2, hy.1.1.le, hy.1.2.le⟩
    have hfin : volume (U ∩ Metric.closedBall x r) ≠ ⊤ := by
      apply ne_top_of_le_ne_top ((isCompact_closedBall x r).measure_ne_top (μ := volume))
      exact measure_mono inter_subset_right
    have hμ := measureReal_mono hsub hfin
    rw [Real.volume_real_closedBall hr0.le]
    apply (le_div_iff₀ (by positivity : 0 < 2 * r)).mpr
    nlinarith
  have h := ge_of_tendsto hr hl
  linarith

/-- Every individual prime-pair tail has full measure on `(1,8)`. -/
theorem ae_mem_primeTail (N : ℕ) :
    ∀ᵐ α : ℝ, 1 < α → α < 8 → α ∈ primeTail N := by
  apply ae_mem_of_local_measure_lower (isOpen_primeTail N).measurableSet
    (κ := 1 / 320000) (by norm_num)
  intro a b ha hab hb
  have h := localTail_measure_lower ha hab hb N
  linarith

/-- For almost every slope between one and eight, the slope is irrational and
there are infinitely many prime inputs with prime floor outputs. -/
theorem ae_irrational_infinite_pairs_between_one_eight :
    ∀ᵐ α : ℝ, 1 < α → α < 8 → Irrational α ∧ (primeSet α).Infinite := by
  have htails : ∀ᵐ α : ℝ, ∀ N : ℕ, 1 < α → α < 8 → α ∈ primeTail N :=
    ae_all_iff.mpr ae_mem_primeTail
  filter_upwards [htails, ae_irrational] with α hα hI
  intro hα1 hα8
  exact ⟨hI, (infinite_iff_mem_all_primeTail (by linarith) hI).mpr
    (fun N => hα N hα1 hα8)⟩

#print axioms ae_irrational_infinite_pairs_between_one_eight

end Erdos972AlmostEverywherePairs
