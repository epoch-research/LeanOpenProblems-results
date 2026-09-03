import Submission.WideTailMeasure
import Submission.AlmostEverywherePairs

/-!
For almost every slope, the genuine prime-pair correlation is at least a
fixed positive multiple of N at arbitrarily large scales. The quantifier is
almost everywhere, not every irrational slope.
-/
namespace Erdos972MetricFrequentLinear

open Finset MeasureTheory Filter
open scoped Topology
open Erdos972ChebyshevLower Erdos972RichSlopes Erdos972Topology
open Erdos972WideMetricSieve Erdos972WideSieveBound Erdos972WidePairWeights
open Erdos972WideLocalMoment Erdos972WideTailMeasure

noncomputable def richTail (A B : ℕ) : Set ℝ :=
  {α | ∃ N : ℕ, B < N ∧ (N : ℝ) / 16 < widePairs A N α}

lemma measurable_widePairs (A N : ℕ) : Measurable (widePairs A N) := by
  classical
  unfold widePairs pairBox
  fun_prop (disch := exact measurableSet_Ico)

lemma measurableSet_richTail (A B : ℕ) : MeasurableSet (richTail A B) := by
  have he : richTail A B = ⋃ N : ℕ, ⋃ (_ : B < N),
      {α | (N : ℝ) / 16 < widePairs A N α} := by
    ext α
    simp [richTail]
  rw [he]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iUnion fun _ =>
    measurableSet_lt measurable_const (measurable_widePairs A N)

lemma localRich_measure_ne_top (a b : ℝ) (A B : ℕ) :
    volume (Set.Ioo a b ∩ richTail A B) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (show volume (Set.Ioo a b) ≠ ⊤ by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  exact measure_mono Set.inter_subset_left

lemma setIntegral_widePairs_rich_upper (A : ℕ) (hA : 1 ≤ A)
    {a b : ℝ} (ha : 1 < a) (hab : a < b) (hb : b < (A : ℝ))
    (B : ℕ) {v : ℕ} (hv : 2 ≤ v) (hAv : A ≤ v) (hBv : B < v^40) :
    (∫ α in Set.Ioo a b, widePairs A (v^40) α) ≤
      (b-a) * (v : ℝ)^40 / 16 +
      volume.real (Set.Ioo a b ∩ richTail A B) * (40000 * (v : ℝ)^40) +
      (v : ℝ)^40 * (82 * (A + 3) * Real.log 4 / (v : ℝ)^3) := by
  let C : ℝ := 40000 * (v : ℝ)^40
  let U : ℝ := Real.log 4 * (v : ℝ)^40 * Real.log ((A : ℝ) * (v : ℝ)^40)
  let f₀ : ℝ → ℝ := (Set.Ioo a b).indicator (fun _ => (v : ℝ)^40 / 16)
  let f : ℝ → ℝ := (Set.Ioo a b ∩ richTail A B).indicator (fun _ => C)
  let g : ℝ → ℝ := (wideBadSlopes A (v^24) (v^28)).indicator (fun _ => U)
  have hA1R : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hv1 : 1 ≤ v := by omega
  have hN2 : 2 ≤ v^40 := hv.trans (by simpa using Nat.pow_le_pow_right hv1 (show 1 ≤ 40 by omega))
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hU : 0 ≤ U := by
    dsimp [U]
    have hl : 0 ≤ Real.log ((A : ℝ) * (v : ℝ)^40) := Real.log_nonneg (by nlinarith [one_le_pow₀ (n := 40) hvR])
    positivity
  have hf₀ : Integrable f₀ :=
    (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ioo
  have hf : Integrable f :=
    (integrableOn_const (localRich_measure_ne_top a b A B)).integrable_indicator
      (measurableSet_Ioo.inter (measurableSet_richTail A B))
  have hg : Integrable g :=
    (integrableOn_const (wideBadSlopes_measure_ne_top A _ _)).integrable_indicator (measurableSet_wideBadSlopes A _ _)
  have hpoint : (Set.Ioo a b).indicator (widePairs A (v^40)) ≤ᵐ[volume]
      (fun α => f₀ α + f α + g α) := by
    apply Eventually.of_forall
    intro α
    change (Set.Ioo a b).indicator (widePairs A (v^40)) α ≤ f₀ α + f α + g α
    have hf₀0 : 0 ≤ f₀ α := Set.indicator_nonneg (by intros; positivity) α
    have hf0 : 0 ≤ f α := Set.indicator_nonneg (fun _ _ => hC) α
    have hg0 : 0 ≤ g α := Set.indicator_nonneg (fun _ _ => hU) α
    by_cases hα : α ∈ Set.Ioo a b
    · rw [Set.indicator_of_mem hα]
      have hα1 : 1 < α := ha.trans hα.1
      have hα9 : α < (A : ℝ) + 1 := by linarith [hα.2]
      by_cases hbad : α ∈ wideBadSlopes A (v^24) (v^28)
      · have hgu : g α = U := Set.indicator_of_mem hbad _
        have hu := widePairs_uniform_upper A hA hN2 α
        push_cast at hu
        change widePairs A (v^40) α ≤ U at hu
        rw [hgu]
        linarith
      · by_cases htail : α ∈ richTail A B
        · have hfc : f α = C := Set.indicator_of_mem (show α ∈ Set.Ioo a b ∩ richTail A B from ⟨hα, htail⟩) _
          have hc := widePairs_power_upper A hA hα1 hα9 hv hAv hbad
          change widePairs A (v^40) α ≤ C at hc
          rw [hfc]
          linarith
        · have hp : widePairs A (v^40) α ≤ (v : ℝ)^40 / 16 := by
            apply le_of_not_gt
            intro h
            exact htail ⟨v^40, hBv, by simpa using h⟩
          have hfc₀ : f₀ α = (v : ℝ)^40 / 16 := Set.indicator_of_mem hα _
          rw [hfc₀]
          linarith
    · rw [Set.indicator_of_notMem hα]
      positivity
  have hi := integral_mono_ae ((integrable_widePairs A _).indicator measurableSet_Ioo)
    ((hf₀.add hf).add hg) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_indicator measurableSet_Ioo,
    integral_add (f := fun α => f₀ α + f α) (hf₀.add hf) hg,
    integral_add hf₀ hf] at hi
  dsimp [f₀, f, g] at hi
  rw [integral_indicator_const _ measurableSet_Ioo,
    integral_indicator_const _ (measurableSet_Ioo.inter (measurableSet_richTail A B)),
    integral_indicator_const _ (measurableSet_wideBadSlopes A _ _),
    Real.volume_real_Ioo, max_eq_left (sub_nonneg.mpr hab.le)] at hi
  simp only [smul_eq_mul] at hi
  have herr := wideBadSlopes_weighted_error A hA hv hAv
  dsimp [C, U] at hi
  linarith

lemma localRich_measure_lower (A : ℕ) (hA : 1 ≤ A) {a b : ℝ}
    (ha : 1 < a) (hab : a < b) (hb : b < (A : ℝ)) (B : ℕ) :
    (b - a) / 640000 ≤ volume.real (Set.Ioo a b ∩ richTail A B) := by
  let m : ℝ := volume.real (Set.Ioo a b ∩ richTail A B)
  have h40 : Tendsto (fun v : ℕ => v^40) atTop atTop := tendsto_id.atTop_pow (by norm_num)
  have h3 : Tendsto (fun v : ℕ => v^3) atTop atTop := tendsto_id.atTop_pow (by norm_num)
  have hE : Tendsto (fun v : ℕ => (82 * (A + 3) * Real.log 4) / (v : ℝ)^3) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using
      (tendsto_const_div_atTop_nhds_zero_nat (82 * (A + 3) * Real.log 4)).comp h3
  have hlim : Tendsto (fun v : ℕ => (b-a)/16 + 40000*m +
      (82 * (A + 3) * Real.log 4) / (v : ℝ)^3) atTop (𝓝 ((b-a)/16 + 40000*m)) := by
    simpa using hE.const_add ((b-a)/16 + 40000*m)
  have hevent : ∀ᶠ v : ℕ in atTop, (b-a)/8 ≤ (b-a)/16 + 40000*m +
      (82 * (A + 3) * Real.log 4) / (v : ℝ)^3 := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_ge_atTop A,
      h40.eventually (eventually_gt_atTop B),
      h40.eventually (eventually_setIntegral_widePairs_lower A ha hab hb)] with v hv hAv hBv hlower
    have hpow : 0 < (v : ℝ)^40 := by positivity
    have hu := setIntegral_widePairs_rich_upper A hA ha hab hb B hv hAv hBv
    push_cast at hlower
    change (∫ α in Set.Ioo a b, widePairs A (v^40) α) ≤ _ + m * _ + _ at hu
    apply (mul_le_mul_iff_left₀ hpow).mp
    nlinarith
  have hbound := ge_of_tendsto hlim hevent
  dsimp [m] at hbound
  linarith

lemma ae_mem_richTail (A B : ℕ) (hA : 1 ≤ A) :
    ∀ᵐ α : ℝ, 1 < α → α < A → α ∈ richTail A B := by
  apply Erdos972AlmostEverywherePairs.ae_mem_of_local_measure_lower
    (measurableSet_richTail A B) (κ := 1 / 640000) (by norm_num)
  intro a b ha hab hb
  have h := localRich_measure_lower A hA ha hab hb B
  linarith

/-- Genuine prime-pair weighted mass, not bounded-almost-prime mass. This is
an almost-everywhere theorem and does not exclude individual bad irrationals. -/
theorem ae_frequently_linear_widePairs :
    ∀ᵐ α : ℝ, ∀ A : ℕ, 1 < α → α < A →
      ∀ B : ℕ, ∃ N : ℕ, B < N ∧ (N : ℝ)/16 < widePairs A N α := by
  have h : ∀ᵐ α : ℝ, ∀ A B : ℕ, 1 ≤ A → 1 < α → α < A → α ∈ richTail A B := by
    apply ae_all_iff.mpr
    intro A
    apply ae_all_iff.mpr
    intro B
    by_cases hA : 1 ≤ A
    · filter_upwards [ae_mem_richTail A B hA] with α hα
      exact fun _ => hα
    · exact Eventually.of_forall fun _ h => (hA h).elim
  filter_upwards [h] with α hα
  intro A hα1 hαA B
  have hA : 1 ≤ A := by exact_mod_cast (show (1 : ℝ) ≤ A by linarith)
  exact hα A B hA hα1 hαA

#print axioms localRich_measure_lower
#print axioms ae_frequently_linear_widePairs

end Erdos972MetricFrequentLinear
