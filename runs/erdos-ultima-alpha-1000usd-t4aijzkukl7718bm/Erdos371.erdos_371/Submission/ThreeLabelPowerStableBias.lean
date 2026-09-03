import Submission.ThreeLabelExactDilationBias
import Submission.RadicalExactDilationBias

/-! An auxiliary three-label family with biased natural order comparisons,
exact eventual fixed-multiplier invariance, and exact positive-power invariance.
This is not a statement about the actual largest-prime-factor labels. -/
namespace Erdos371.ExactMultiplierChirpObstruction
open Finset Filter
open scoped Topology

/-- Finite quantization and a three-label projection preserve a fixed amount
of imaginary correlation bias. Every identity preserved by composition can
then be retained by the resulting label maps. -/
theorem exists_three_label_maps_of_imaginary_bias {J : Type*}
    (N : J → ℕ) (F : J → ℕ → ℂ) (hF : ∀ j n, ‖F j n‖ ≤ 1)
    (β : ℝ) (hβ : 0 < β) (hbias : ∀ j, β ≤ imaginaryBias (F j) (N j)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ T : J → ℂ → Fin 3,
      ∀ j, orderedMean (T j ∘ F j) (N j) ≤ -δ := by
  obtain ⟨Q,v,q,hv,hq⟩ := finite_unitBall_quantizer (β/8) (by positivity)
  have hproj (j : J) : ∃ R : Fin Q → Fin 3,
      orderedMean (R ∘ q ∘ F j) (N j) ≤ -(β/2)/((Q : ℝ)^2+1) := by
    have hNj : 0 < N j := by
      by_contra h
      have hz : N j = 0 := by omega
      have hb := hbias j
      norm_num [imaginaryBias,hz] at hb
      linarith
    let G := fun n => v (q (F j n))
    have herr := imaginaryBias_uniform_error G (F j) (fun n => hv _) (hF j) (β/8)
      (fun n => (hq (F j n) (hF j n)).le) (N j) hNj
    have hG : β/2 ≤ imaginaryBias G (N j) := by
      have hlo := (abs_le.mp herr).1
      linarith [hbias j]
    have hmean : β/2 ≤ (∑ n ∈ Icc 1 (N j), phaseSkew v (q (F j n)) (q (F j (n+1))))/(N j) := hG
    simpa only [Fintype.card_fin] using exists_negative_three_label_projection (q ∘ F j)
      (phaseSkew v) (phaseSkew_swap v) (phaseSkew_abs_le v hv) (N j) (β/2) (by positivity) hmean
  choose R hR using hproj
  refine ⟨(β/2)/((Q : ℝ)^2+1),by positivity,fun j => R j ∘ q,?_⟩
  intro j
  simpa only [Function.comp_assoc,neg_div] using hR j

/-- Both fixed-multiplier and positive-power invariance still fall short of
the arithmetic max-under-multiplication structure. This countermodel has a
fixed three-element ordered alphabet and a fixed natural rise deficit. -/
theorem exists_three_label_power_stable_rise_deficit :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ → ℕ, ∃ L : ℕ → ℕ → Fin 3,
      Tendsto N atTop atTop ∧
      (∀ j k, 0 < k → k ≤ j → ∀ n, L j (k*n) = L j n) ∧
      (∀ j n r, 0 < r → L j (n^r) = L j n) ∧
      (∀ j, orderedMean (L j) (N j) ≤ -δ) ∧
      ∀ j, (((Icc 1 (N j)).filter fun n => L j n < L j (n+1)).card : ℝ)/(N j) ≤ 1/2-δ/2 := by
  obtain ⟨N,F,hN,hF,hstable,hpow,hbias⟩ := exists_exact_dilation_and_power_stable_biased_family
  obtain ⟨δ,hδ,T,hT⟩ := exists_three_label_maps_of_imaginary_bias N F hF
    (1/240) (by norm_num) hbias
  refine ⟨δ,hδ,N,fun j => T j ∘ F j,hN,?_,?_,hT,?_⟩
  · intro j k hk hkj n
    dsimp only [Function.comp_apply]
    rw [hstable j k hk hkj n]
  · intro j n r hr
    dsimp only [Function.comp_apply]
    rw [hpow j n r hr]
  · intro j
    have hNj : 0 < N j := by
      by_contra h
      have hz : N j = 0 := by omega
      have hb := hT j
      norm_num [orderedMean,hz] at hb
      linarith
    have hb := rising_fraction_le_orderedMean (T j ∘ F j) (N j) hNj
    change (((Icc 1 (N j)).filter fun n => (T j ∘ F j) n < (T j ∘ F j) (n+1)).card : ℝ)/(N j) ≤ _
    linarith [hT j]

#print axioms exists_three_label_maps_of_imaginary_bias
#print axioms exists_three_label_power_stable_rise_deficit
end Erdos371.ExactMultiplierChirpObstruction
