import Submission.WideSieveBound
import Submission.WideLocalMoment
import Submission.LocalTailMeasure

/-! Uniform local relative-measure bounds for all bounded slope ranges. -/
namespace Erdos972WideTailMeasure

open Finset MeasureTheory Filter
open Erdos972ChebyshevLower Erdos972RichSlopes Erdos972Topology
open Erdos972WideMetricSieve Erdos972WideSieveBound Erdos972WidePairWeights Erdos972WideLocalMoment
open Erdos972LocalTailMeasure (localTail_measure_ne_top localTail_measurable)

lemma wideBadSlopes_power_measure (A : ℕ) {v : ℕ} (hv : 0 < v) :
    volume.real (wideBadSlopes A (v^24) (v^28)) ≤ (2 * (A + 3) : ℝ) / (v : ℝ)^4 := by
  have hvR : (v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hv.ne'
  have h := wideBadSlopes_measure_le A (v^24) (v^28) (by positivity)
  push_cast at h
  convert h using 1
  field_simp

lemma wideBadSlopes_weighted_error (A : ℕ) (hA : 1 ≤ A) {v : ℕ} (hv : 2 ≤ v) (hAv : A ≤ v) :
    volume.real (wideBadSlopes A (v^24) (v^28)) *
      (Real.log 4 * (v : ℝ)^40 * Real.log ((A : ℝ) * (v : ℝ)^40)) ≤
        (v : ℝ)^40 * (82 * (A + 3) * Real.log 4 / (v : ℝ)^3) := by
  have hv0 : (0 : ℝ) < v := Nat.cast_pos.mpr (by omega)
  have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast (show 1 ≤ v by omega)
  have hA0 : (0 : ℝ) < A := Nat.cast_pos.mpr (by omega)
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hAvR : (A : ℝ) ≤ v := Nat.cast_le.mpr hAv
  have hlog : Real.log ((A : ℝ) * (v : ℝ)^40) ≤ 41 * v := by
    rw [Real.log_mul hA0.ne' (pow_ne_zero _ hv0.ne'), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_sub_one_of_pos hv0, Real.log_le_log hA0 hAvR]
  have hlog0 : 0 ≤ Real.log ((A : ℝ) * (v : ℝ)^40) :=
    Real.log_nonneg (by nlinarith [one_le_pow₀ (n := 40) hv1])
  calc
    _ ≤ ((2 * (A + 3) : ℝ) / (v : ℝ)^4) * (Real.log 4 * (v : ℝ)^40 * (41 * v)) := by
      apply mul_le_mul (wideBadSlopes_power_measure A (by omega))
      · exact mul_le_mul_of_nonneg_left hlog (by positivity)
      · positivity
      · positivity
    _ = _ := by field_simp; ring

lemma setIntegral_widePairs_upper (A : ℕ) (hA : 1 ≤ A) {a b : ℝ} (ha : 1 < a) (hb : b < (A : ℝ))
    (B : ℕ) {v : ℕ} (hv : 2 ≤ v) (hAv : A ≤ v) :
    (∫ α in Set.Ioo a b, widePairs A (v^40) α) ≤ (∫ α : ℝ, widePairs A B α) +
      volume.real (Set.Ioo a b ∩ primeTail B) * (40000 * (v : ℝ)^40) +
      (v : ℝ)^40 * (82 * (A + 3) * Real.log 4 / (v : ℝ)^3) := by
  let C : ℝ := 40000 * (v : ℝ)^40
  let U : ℝ := Real.log 4 * (v : ℝ)^40 * Real.log ((A : ℝ) * (v : ℝ)^40)
  let f : ℝ → ℝ := (Set.Ioo a b ∩ primeTail B).indicator (fun _ => C)
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
  have hf : Integrable f :=
    (integrableOn_const (localTail_measure_ne_top a b B)).integrable_indicator (localTail_measurable a b B)
  have hg : Integrable g :=
    (integrableOn_const (wideBadSlopes_measure_ne_top A _ _)).integrable_indicator (measurableSet_wideBadSlopes A _ _)
  have hpoint : (Set.Ioo a b).indicator (widePairs A (v^40)) ≤ᵐ[volume]
      (fun α => widePairs A B α + f α + g α) := by
    filter_upwards [ae_irrational] with α hI
    have hf0 : 0 ≤ f α := Set.indicator_nonneg (fun _ _ => hC) α
    have hg0 : 0 ≤ g α := Set.indicator_nonneg (fun _ _ => hU) α
    have hB0 := widePairs_nonneg A B α
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
      · by_cases htail : α ∈ primeTail B
        · have hfc : f α = C := Set.indicator_of_mem (show α ∈ Set.Ioo a b ∩ primeTail B from ⟨hα, htail⟩) _
          have hc := widePairs_power_upper A hA hα1 hα9 hv hAv hbad
          change widePairs A (v^40) α ≤ C at hc
          rw [hfc]
          linarith
        · have hp := widePairs_le_of_not_mem_primeTail A (by linarith) hI (v^40) B htail
          linarith
    · rw [Set.indicator_of_notMem hα]
      positivity
  have hi := integral_mono_ae ((integrable_widePairs A _).indicator measurableSet_Ioo)
    (((integrable_widePairs A B).add hf).add hg) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_indicator measurableSet_Ioo,
    integral_add (f := fun α => widePairs A B α + f α) ((integrable_widePairs A B).add hf) hg,
    integral_add (integrable_widePairs A B) hf] at hi
  dsimp [f, g] at hi
  rw [integral_indicator_const _ (localTail_measurable a b B),
    integral_indicator_const _ (measurableSet_wideBadSlopes A _ _)] at hi
  simp only [smul_eq_mul] at hi
  have herr := wideBadSlopes_weighted_error A hA hv hAv
  dsimp [C, U] at hi
  linarith

/-- The same positive proportion works in every fixed interval within `(1,8)`.
This is stronger than merely knowing that the good slopes have positive measure. -/
theorem localTail_measure_lower (A : ℕ) (hA : 1 ≤ A) {a b : ℝ} (ha : 1 < a) (hab : a < b) (hb : b < (A : ℝ)) (B : ℕ) :
    (b - a) / 320000 ≤ volume.real (Set.Ioo a b ∩ primeTail B) := by
  let I : ℝ := ∫ α : ℝ, widePairs A B α
  let m : ℝ := volume.real (Set.Ioo a b ∩ primeTail B)
  have h40 : Tendsto (fun v : ℕ => v^40) atTop atTop := tendsto_id.atTop_pow (by norm_num)
  have h3 : Tendsto (fun v : ℕ => v^3) atTop atTop := tendsto_id.atTop_pow (by norm_num)
  have hI : Tendsto (fun v : ℕ => I / (v : ℝ)^40) atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using (tendsto_const_div_atTop_nhds_zero_nat I).comp h40
  have hE : Tendsto (fun v : ℕ => (82 * (A + 3) * Real.log 4) / (v : ℝ)^3) atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using
      (tendsto_const_div_atTop_nhds_zero_nat (82 * (A + 3) * Real.log 4)).comp h3
  have hlim : Tendsto (fun v : ℕ => I / (v : ℝ)^40 + (82 * (A + 3) * Real.log 4) / (v : ℝ)^3 +
      40000 * m) atTop (nhds (40000 * m)) := by
    simpa using (hI.add hE).add_const (40000 * m)
  have hevent : ∀ᶠ v : ℕ in atTop, (b - a) / 8 ≤
      I / (v : ℝ)^40 + (82 * (A + 3) * Real.log 4) / (v : ℝ)^3 + 40000 * m := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_ge_atTop A,
      h40.eventually (eventually_setIntegral_widePairs_lower A ha hab hb)] with v hv hAv hlower
    have hv0 : (0 : ℝ) < v := Nat.cast_pos.mpr (by omega)
    have hpow : 0 < (v : ℝ)^40 := by positivity
    have hu := setIntegral_widePairs_upper A hA ha hb B hv hAv
    push_cast at hlower
    have hIeq : (I / (v : ℝ)^40) * (v : ℝ)^40 = I := div_mul_cancel₀ _ hpow.ne'
    change (∫ α in Set.Ioo a b, widePairs A (v^40) α) ≤ I + m * _ + _ at hu
    nlinarith
  have hbound := ge_of_tendsto hlim hevent
  dsimp [m] at hbound
  linarith


#print axioms localTail_measure_lower
end Erdos972WideTailMeasure
