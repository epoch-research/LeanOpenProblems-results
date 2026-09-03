import Submission.LocalFirstMoment

/-! Uniform positive relative measure of every prime-pair tail on each fixed
interior slope interval. -/
namespace Erdos972LocalTailMeasure

open Finset MeasureTheory Filter
open Erdos972ChebyshevLower Erdos972RichSlopes Erdos972MetricRichness
open Erdos972MetricSieve Erdos972MetricSieveBound Erdos972MetricInfinitePairs
open Erdos972Topology Erdos972LocalFirstMoment

lemma localTail_measure_ne_top (a b : ℝ) (B : ℕ) :
    volume (Set.Ioo a b ∩ primeTail B) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (show volume (Set.Ioo a b) ≠ ⊤ by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  exact measure_mono Set.inter_subset_left

lemma localTail_measurable (a b : ℝ) (B : ℕ) :
    MeasurableSet (Set.Ioo a b ∩ primeTail B) :=
  measurableSet_Ioo.inter (isOpen_primeTail B).measurableSet

lemma setIntegral_weightedPairs_upper {a b : ℝ} (ha : 1 < a) (hb : b < 8)
    (B : ℕ) {v : ℕ} (hv : 2 ≤ v) :
    (∫ α in Set.Ioo a b, weightedPairs (v^40) α) ≤ (∫ α : ℝ, weightedPairs B α) +
      volume.real (Set.Ioo a b ∩ primeTail B) * (40000 * (v : ℝ)^40) +
      (v : ℝ)^40 * (968 * Real.log 4 / (v : ℝ)^3) := by
  let C : ℝ := 40000 * (v : ℝ)^40
  let U : ℝ := Real.log 4 * (v : ℝ)^40 * Real.log (8 * (v : ℝ)^40)
  let f : ℝ → ℝ := (Set.Ioo a b ∩ primeTail B).indicator (fun _ => C)
  let g : ℝ → ℝ := (badSlopes (v^24) (v^28)).indicator (fun _ => U)
  have hv1 : 1 ≤ v := by omega
  have hN2 : 2 ≤ v^40 := hv.trans (by simpa using Nat.pow_le_pow_right hv1 (show 1 ≤ 40 by omega))
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hU : 0 ≤ U := by
    dsimp [U]
    have hl : 0 ≤ Real.log (8 * (v : ℝ)^40) := Real.log_nonneg (by nlinarith [one_le_pow₀ (n := 40) hvR])
    positivity
  have hf : Integrable f :=
    (integrableOn_const (localTail_measure_ne_top a b B)).integrable_indicator (localTail_measurable a b B)
  have hg : Integrable g :=
    (integrableOn_const (badSlopes_measure_ne_top _ _)).integrable_indicator (measurableSet_badSlopes _ _)
  have hpoint : (Set.Ioo a b).indicator (weightedPairs (v^40)) ≤ᵐ[volume]
      (fun α => weightedPairs B α + f α + g α) := by
    filter_upwards [ae_irrational] with α hI
    have hf0 : 0 ≤ f α := Set.indicator_nonneg (fun _ _ => hC) α
    have hg0 : 0 ≤ g α := Set.indicator_nonneg (fun _ _ => hU) α
    have hB0 := weightedPairs_nonneg B α
    by_cases hα : α ∈ Set.Ioo a b
    · rw [Set.indicator_of_mem hα]
      have hα1 : 1 < α := ha.trans hα.1
      have hα9 : α < 9 := by linarith [hα.2]
      by_cases hbad : α ∈ badSlopes (v^24) (v^28)
      · have hgu : g α = U := Set.indicator_of_mem hbad _
        have hu := weightedPairs_uniform_upper hN2 α
        push_cast at hu
        change weightedPairs (v^40) α ≤ U at hu
        rw [hgu]
        linarith
      · by_cases htail : α ∈ primeTail B
        · have hfc : f α = C := Set.indicator_of_mem (show α ∈ Set.Ioo a b ∩ primeTail B from ⟨hα, htail⟩) _
          have hc := weightedPairs_power_upper hα1 hα9 hv hbad
          change weightedPairs (v^40) α ≤ C at hc
          rw [hfc]
          linarith
        · have hp := weightedPairs_le_of_not_mem_primeTail (by linarith) hI (v^40) B htail
          linarith
    · rw [Set.indicator_of_notMem hα]
      positivity
  have hi := integral_mono_ae ((integrable_weightedPairs _).indicator measurableSet_Ioo)
    (((integrable_weightedPairs B).add hf).add hg) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_indicator measurableSet_Ioo,
    integral_add (f := fun α => weightedPairs B α + f α) ((integrable_weightedPairs B).add hf) hg,
    integral_add (integrable_weightedPairs B) hf] at hi
  dsimp [f, g] at hi
  rw [integral_indicator_const _ (localTail_measurable a b B),
    integral_indicator_const _ (measurableSet_badSlopes _ _)] at hi
  simp only [smul_eq_mul] at hi
  have herr := badSlopes_weighted_error hv
  dsimp [C, U] at hi
  linarith

/-- The same positive proportion works in every fixed interval within `(1,8)`.
This is stronger than merely knowing that the good slopes have positive measure. -/
theorem localTail_measure_lower {a b : ℝ} (ha : 1 < a) (hab : a < b) (hb : b < 8) (B : ℕ) :
    (b - a) / 320000 ≤ volume.real (Set.Ioo a b ∩ primeTail B) := by
  let I : ℝ := ∫ α : ℝ, weightedPairs B α
  let m : ℝ := volume.real (Set.Ioo a b ∩ primeTail B)
  have h40 : Tendsto (fun v : ℕ => v^40) atTop atTop := tendsto_id.atTop_pow (by norm_num)
  have h3 : Tendsto (fun v : ℕ => v^3) atTop atTop := tendsto_id.atTop_pow (by norm_num)
  have hI : Tendsto (fun v : ℕ => I / (v : ℝ)^40) atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using (tendsto_const_div_atTop_nhds_zero_nat I).comp h40
  have hE : Tendsto (fun v : ℕ => (968 * Real.log 4) / (v : ℝ)^3) atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using
      (tendsto_const_div_atTop_nhds_zero_nat (968 * Real.log 4)).comp h3
  have hlim : Tendsto (fun v : ℕ => I / (v : ℝ)^40 + (968 * Real.log 4) / (v : ℝ)^3 +
      40000 * m) atTop (nhds (40000 * m)) := by
    simpa using (hI.add hE).add_const (40000 * m)
  have hevent : ∀ᶠ v : ℕ in atTop, (b - a) / 8 ≤
      I / (v : ℝ)^40 + (968 * Real.log 4) / (v : ℝ)^3 + 40000 * m := by
    filter_upwards [eventually_ge_atTop (2 : ℕ),
      h40.eventually (eventually_setIntegral_weightedPairs_lower ha hab hb)] with v hv hlower
    have hv0 : (0 : ℝ) < v := Nat.cast_pos.mpr (by omega)
    have hpow : 0 < (v : ℝ)^40 := by positivity
    have hu := setIntegral_weightedPairs_upper ha hb B hv
    push_cast at hlower
    have hIeq : (I / (v : ℝ)^40) * (v : ℝ)^40 = I := div_mul_cancel₀ _ hpow.ne'
    change (∫ α in Set.Ioo a b, weightedPairs (v^40) α) ≤ I + m * _ + _ at hu
    nlinarith
  have hbound := ge_of_tendsto hlim hevent
  dsimp [m] at hbound
  linarith

#print axioms localTail_measure_lower

end Erdos972LocalTailMeasure
