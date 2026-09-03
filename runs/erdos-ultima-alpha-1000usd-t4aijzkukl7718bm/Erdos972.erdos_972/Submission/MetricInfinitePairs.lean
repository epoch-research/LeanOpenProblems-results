import Submission.MetricSieveBound
import Submission.TailTopology

/-!
A positive-measure infinitude result from the first moment and a two-coordinate
upper sieve. This does not settle individual exceptional irrational slopes.
-/
namespace Erdos972MetricInfinitePairs

open Finset MeasureTheory Filter
open Erdos972ChebyshevLower Erdos972RichSlopes Erdos972MetricRichness
open Erdos972MetricSieve Erdos972MetricSieveBound Erdos972Topology

lemma weightedPairs_mono (α : ℝ) : Monotone (fun N => weightedPairs N α) := by
  intro N M hNM
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpI, hprime⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hpI).1, (mem_Ioc.mp hpI).2.trans hNM⟩, hprime⟩
  · intro p hp _
    have hpp := (mem_filter.mp hp).2
    apply sum_nonneg
    intro q hq
    apply Set.indicator_nonneg
    intro _ _
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_le))
      (Real.log_nonneg (by exact_mod_cast (mem_filter.mp hq).2.one_le))

lemma weightedPairs_le_of_not_mem_primeTail {α : ℝ} (hα : 0 ≤ α) (hI : Irrational α)
    (N B : ℕ) (hbad : α ∉ primeTail B) : weightedPairs N α ≤ weightedPairs B α := by
  classical
  by_cases hNB : N ≤ B
  · exact weightedPairs_mono α hNB
  have hBN : B ≤ N := by omega
  have heq : weightedPairs B α = weightedPairs N α := by
    apply sum_subset
    · intro p hp
      obtain ⟨hpI, hprime⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hpI).1, (mem_Ioc.mp hpI).2.trans hBN⟩, hprime⟩
    · intro p hp hpB
      have hpp := (mem_filter.mp hp).2
      have hp0 := (mem_Ioc.mp (mem_filter.mp hp).1).1
      have hBp : B < p := by
        by_contra h
        exact hpB (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp0, Nat.le_of_not_gt h⟩, hpp⟩)
      apply sum_eq_zero
      intro q hq
      apply pairBox_eq_zero_of_ne_floor hpp.pos
      intro hfloor
      have hqp : (⌊α * p⌋₊).Prime := hfloor ▸ (mem_filter.mp hq).2
      apply hbad
      refine ⟨p, ⌊α * p⌋₊, hBp, hpp, hqp, ?_, Nat.lt_floor_add_one _⟩
      exact lt_of_le_of_ne (Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg p)))
        ((hI.mul_natCast hpp.ne_zero).ne_nat _).symm
  exact heq.ge

def tailSlopes (B : ℕ) : Set ℝ := Set.Ioo 1 9 ∩ primeTail B

lemma measurableSet_tailSlopes (B : ℕ) : MeasurableSet (tailSlopes B) :=
  measurableSet_Ioo.inter (isOpen_primeTail B).measurableSet

lemma tailSlopes_measure_ne_top (B : ℕ) : volume (tailSlopes B) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (show volume (Set.Ioo (1 : ℝ) 9) ≠ ⊤ by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  exact measure_mono Set.inter_subset_left

lemma integral_weightedPairs_le_tail_bad (B : ℕ) {v : ℕ} (hv : 2 ≤ v) :
    (∫ α : ℝ, weightedPairs (v^40) α) ≤ (∫ α : ℝ, weightedPairs B α) +
      volume.real (tailSlopes B) * (40000 * (v : ℝ)^40) +
      volume.real (badSlopes (v^24) (v^28)) *
        (Real.log 4 * (v : ℝ)^40 * Real.log (8 * (v : ℝ)^40)) := by
  let C : ℝ := 40000 * (v : ℝ)^40
  let U : ℝ := Real.log 4 * (v : ℝ)^40 * Real.log (8 * (v : ℝ)^40)
  let f : ℝ → ℝ := (tailSlopes B).indicator (fun _ => C)
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
    (integrableOn_const (tailSlopes_measure_ne_top B)).integrable_indicator (measurableSet_tailSlopes B)
  have hg : Integrable g :=
    (integrableOn_const (badSlopes_measure_ne_top _ _)).integrable_indicator (measurableSet_badSlopes _ _)
  have hpoint : (fun α => weightedPairs (v^40) α) ≤ᵐ[volume]
      (fun α => weightedPairs B α + f α + g α) := by
    filter_upwards [ae_irrational] with α hI
    have hf0 : 0 ≤ f α := Set.indicator_nonneg (fun _ _ => hC) α
    have hg0 : 0 ≤ g α := Set.indicator_nonneg (fun _ _ => hU) α
    have hB0 := weightedPairs_nonneg B α
    by_cases hα : α ∈ Set.Ioo (1 : ℝ) 9
    · by_cases hb : α ∈ badSlopes (v^24) (v^28)
      · have hgu : g α = U := Set.indicator_of_mem hb _
        have hu := weightedPairs_uniform_upper hN2 α
        push_cast at hu
        change weightedPairs (v^40) α ≤ U at hu
        rw [hgu]
        linarith
      · by_cases ht : α ∈ tailSlopes B
        · have hfc : f α = C := Set.indicator_of_mem ht _
          have hc := weightedPairs_power_upper hα.1 hα.2 hv hb
          change weightedPairs (v^40) α ≤ C at hc
          rw [hfc]
          linarith
        · have hn : α ∉ primeTail B := fun h => ht ⟨hα, h⟩
          have hp := weightedPairs_le_of_not_mem_primeTail (by linarith [hα.1]) hI (v^40) B hn
          linarith
    · rw [weightedPairs_eq_zero_of_not_mem _ hα]
      linarith
  have hi := integral_mono_ae (integrable_weightedPairs _) ((integrable_weightedPairs B).add hf |>.add hg) hpoint
  change (∫ α : ℝ, weightedPairs (v^40) α) ≤ (∫ α : ℝ, weightedPairs B α + f α + g α) at hi
  rw [integral_add (f := fun α => weightedPairs B α + f α) ((integrable_weightedPairs B).add hf) hg,
    integral_add (integrable_weightedPairs B) hf] at hi
  dsimp [f, g] at hi
  rw [integral_indicator_const _ (measurableSet_tailSlopes B),
    integral_indicator_const _ (measurableSet_badSlopes _ _)] at hi
  simpa only [smul_eq_mul] using hi

lemma badSlopes_power_measure {v : ℕ} (hv : 0 < v) :
    volume.real (badSlopes (v^24) (v^28)) ≤ 22 / (v : ℝ)^4 := by
  have hvR : (v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hv.ne'
  have h := badSlopes_measure_le (v^24) (v^28) (by positivity)
  push_cast at h
  convert h using 1
  field_simp

lemma badSlopes_weighted_error {v : ℕ} (hv : 2 ≤ v) :
    volume.real (badSlopes (v^24) (v^28)) *
      (Real.log 4 * (v : ℝ)^40 * Real.log (8 * (v : ℝ)^40)) ≤
        (v : ℝ)^40 * (968 * Real.log 4 / (v : ℝ)^3) := by
  have hv0 : (0 : ℝ) < v := Nat.cast_pos.mpr (by omega)
  have hv2 : (2 : ℝ) ≤ v := by exact_mod_cast hv
  have hv1 : (1 : ℝ) ≤ v := by linarith
  have hlog : Real.log (8 * (v : ℝ)^40) ≤ 44 * v := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hv0.ne'), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_sub_one_of_pos hv0,
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)]
  have hlog0 : 0 ≤ Real.log (8 * (v : ℝ)^40) :=
    Real.log_nonneg (by nlinarith [one_le_pow₀ (n := 40) hv1])
  calc
    _ ≤ (22 / (v : ℝ)^4) * (Real.log 4 * (v : ℝ)^40 * (44 * v)) := by
      apply mul_le_mul (badSlopes_power_measure (by omega))
      · exact mul_le_mul_of_nonneg_left hlog (by positivity)
      · positivity
      · positivity
    _ = _ := by field_simp; ring

lemma integral_weightedPairs_le_tail (B : ℕ) {v : ℕ} (hv : 2 ≤ v) :
    (∫ α : ℝ, weightedPairs (v^40) α) ≤ (∫ α : ℝ, weightedPairs B α) +
      volume.real (tailSlopes B) * (40000 * (v : ℝ)^40) +
      (v : ℝ)^40 * (968 * Real.log 4 / (v : ℝ)^3) := by
  have h := integral_weightedPairs_le_tail_bad B hv
  have hb := badSlopes_weighted_error hv
  linarith

/-- A uniform positive measure bound for every prime-pair tail. -/
theorem tailSlopes_measure_lower (B : ℕ) :
    Real.log 2 ^ 2 / 80000 ≤ volume.real (tailSlopes B) := by
  let I : ℝ := ∫ α : ℝ, weightedPairs B α
  have h40 : Tendsto (fun v : ℕ => v^40) atTop atTop := tendsto_id.atTop_pow (by norm_num)
  have h3 : Tendsto (fun v : ℕ => v^3) atTop atTop := tendsto_id.atTop_pow (by norm_num)
  have hI : Tendsto (fun v : ℕ => I / (v : ℝ)^40) atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using (tendsto_const_div_atTop_nhds_zero_nat I).comp h40
  have hE : Tendsto (fun v : ℕ => (968 * Real.log 4) / (v : ℝ)^3) atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using
      (tendsto_const_div_atTop_nhds_zero_nat (968 * Real.log 4)).comp h3
  have hlim : Tendsto (fun v : ℕ => I / (v : ℝ)^40 + (968 * Real.log 4) / (v : ℝ)^3 +
      40000 * volume.real (tailSlopes B)) atTop (nhds (40000 * volume.real (tailSlopes B))) := by
    simpa using (hI.add hE).add_const (40000 * volume.real (tailSlopes B))
  have hevent : ∀ᶠ v : ℕ in atTop, Real.log 2 ^ 2 / 2 ≤
      I / (v : ℝ)^40 + (968 * Real.log 4) / (v : ℝ)^3 +
        40000 * volume.real (tailSlopes B) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ),
      h40.eventually eventually_integral_weightedPairs_lower] with v hv hlower
    have hv0 : (0 : ℝ) < v := Nat.cast_pos.mpr (by omega)
    have hpow : 0 < (v : ℝ)^40 := by positivity
    have hu := integral_weightedPairs_le_tail B hv
    push_cast at hlower
    have hIeq : (I / (v : ℝ)^40) * (v : ℝ)^40 = I := div_mul_cancel₀ _ hpow.ne'
    change (∫ α : ℝ, weightedPairs (v^40) α) ≤ I + _ + _ at hu
    nlinarith
  have hbound := ge_of_tendsto hlim hevent
  linarith

/-- Positive Lebesgue measure of fixed irrational slopes with infinitely many
prime pairs. Unlike the category result, this cannot be supported on a null set. -/
theorem positive_measure_infinite_pairs :
    0 < volume {α : ℝ | 1 < α ∧ α < 9 ∧ Irrational α ∧ (primeSet α).Infinite} := by
  have hanti : Antitone tailSlopes := by
    intro B C hBC α hα
    exact ⟨hα.1, primeTail_antitone hBC hα.2⟩
  have hmeasure : volume (⋂ B : ℕ, tailSlopes B) = ⨅ B : ℕ, volume (tailSlopes B) :=
    hanti.measure_iInter (fun B => (measurableSet_tailSlopes B).nullMeasurableSet)
      ⟨0, tailSlopes_measure_ne_top 0⟩
  have hc : 0 < Real.log 2 ^ 2 / 80000 := by positivity
  have hlow : ENNReal.ofReal (Real.log 2 ^ 2 / 80000) ≤ volume (⋂ B : ℕ, tailSlopes B) := by
    rw [hmeasure]
    apply le_iInf
    intro B
    have h := ENNReal.ofReal_le_ofReal (tailSlopes_measure_lower B)
    rwa [Measure.real, ENNReal.ofReal_toReal (tailSlopes_measure_ne_top B)] at h
  have hnull : volume {α : ℝ | Irrational α}ᶜ = 0 := by
    exact ae_iff.mp ae_irrational
  have heq : volume ((⋂ B : ℕ, tailSlopes B) ∩ {α : ℝ | Irrational α}) =
      volume (⋂ B : ℕ, tailSlopes B) := measure_inter_conull hnull
  have hsub : ((⋂ B : ℕ, tailSlopes B) ∩ {α : ℝ | Irrational α}) ⊆
      {α : ℝ | 1 < α ∧ α < 9 ∧ Irrational α ∧ (primeSet α).Infinite} := by
    intro α hα
    have ht := Set.mem_iInter.mp hα.1
    have hI := hα.2
    have hb := (ht 0).1
    refine ⟨hb.1, hb.2, hI, ?_⟩
    apply (infinite_iff_mem_all_primeTail (by linarith [hb.1]) hI).mpr
    intro B
    exact (ht B).2
  apply (ENNReal.ofReal_pos.mpr hc).trans_le
  apply hlow.trans
  rw [← heq]
  exact measure_mono hsub

#print axioms tailSlopes_measure_lower
#print axioms positive_measure_infinite_pairs

end Erdos972MetricInfinitePairs
