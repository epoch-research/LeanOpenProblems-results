import Submission.FixedStableBias
import Submission.PrimeWinnerHarmonicLimits

/-! Even absolute harmonic summability of every fixed-multiplier defect
cannot upgrade harmonic skew cancellation to ordinary cancellation. This
is an auxiliary fixed three-label countermodel, NOT a disproof of Erdős 371.
No maximum-under-multiplication property is asserted. -/
namespace Erdos371.ExactMultiplierChirpObstruction
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

/-- Composition preserves the smooth-set support of each dilation defect. -/
lemma fixedBiasedPhase_comp_defect_harmonic_bound {A : Type*} (g : ℂ → A)
    (k n : ℕ) (hk : 0 < k) :
    ‖labelDilationDefect k (g ∘ fixedBiasedPhase) n / (n : ℝ)‖ ≤
      smoothReciprocal (biasBand k) n := by
  classical
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.cast_zero, div_zero, norm_zero] using
      smoothReciprocal_nonneg (biasBand k) 0
  by_cases hp : Nat.maxPrimeFac n ≤ biasBand k
  · rw [smoothReciprocal_of_maxPrimeFac_le (biasBand k) n hn hp,
      norm_div, Real.norm_natCast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    simpa only [Real.norm_eq_abs] using
      labelDilationDefect_abs_le k (g ∘ fixedBiasedPhase) n
  · have he := fixedBiasedPhase_small_multiplier k n hk (by omega)
    have hz : labelDilationDefect k (g ∘ fixedBiasedPhase) n = 0 := by
      simp [labelDilationDefect, Function.comp_apply, he]
    rw [hz, zero_div, norm_zero]
    exact smoothReciprocal_nonneg (biasBand k) n

/-- Every fixed positive multiplier has an absolutely summable harmonic
sequence of defects, even after arbitrary relabelling. -/
theorem fixedBiasedPhase_comp_summable_harmonic_defects {A : Type*} (g : ℂ → A)
    (k : ℕ) (hk : 0 < k) :
    Summable (fun n => ‖labelDilationDefect k (g ∘ fixedBiasedPhase) n / (n : ℝ)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => fixedBiasedPhase_comp_defect_harmonic_bound g k n hk)
    (summable_smoothReciprocal (biasBand k))


/-- The actual largest-prime label also has absolutely summable harmonic
fixed-multiplier defects. The preceding obstruction therefore concerns a
property genuinely shared by the arithmetic sequence, but not its max law. -/
theorem maxPrimeFac_comp_summable_harmonic_defects {A : Type*} (g : ℕ → A)
    (k : ℕ) (hk : 0 < k) :
    Summable (fun n => ‖labelDilationDefect k (g ∘ Nat.maxPrimeFac) n / (n : ℝ)‖) := by
  classical
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (summable_smoothReciprocal k)
  intro n
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.cast_zero, div_zero, norm_zero] using smoothReciprocal_nonneg k 0
  by_cases hp : Nat.maxPrimeFac n ≤ k
  · rw [smoothReciprocal_of_maxPrimeFac_le k n hn hp, norm_div, Real.norm_natCast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    simpa only [Real.norm_eq_abs] using
      labelDilationDefect_abs_le k (g ∘ Nat.maxPrimeFac) n
  · have he : Nat.maxPrimeFac (k*n) = Nat.maxPrimeFac n := by
      rw [Nat.maxPrimeFac_mul hk.ne' hn, max_eq_right]
      exact (Nat.maxPrimeFac_le (n := k)).trans (by omega)
    have hz : labelDilationDefect k (g ∘ Nat.maxPrimeFac) n = 0 := by
      simp [labelDilationDefect, Function.comp_apply, he]
    rw [hz, zero_div, norm_zero]
    exact smoothReciprocal_nonneg k n

/-- A single fixed three-label map of the fixed phase retains some ordinary
skew nonconvergence. The relabelling is chosen once, not at each endpoint. -/
lemma exists_fixed_three_label_map_nonzero :
    ∃ g : ℂ → Fin 3, ¬Tendsto (orderedMean (g ∘ fixedBiasedPhase)) atTop (𝓝 0) := by
  classical
  obtain ⟨Q,v,q,hv,hq⟩ := finite_unitBall_quantizer (1/10000) (by norm_num)
  let L := q ∘ fixedBiasedPhase
  let C := phaseSkew v
  let D := fun j => biasEndpoint (biasBand j)
  have hbias (j : ℕ) : (1/480 : ℝ) ≤
      (∑ n ∈ Icc 1 (D j), C (L n) (L (n+1))) / D j := by
    have hN : 0 < D j := by
      have := (biasEndpoint_spec (biasBand j)).1
      dsimp [D]
      omega
    have he := imaginaryBias_uniform_error (v ∘ L) fixedBiasedPhase (fun _ => hv _)
      fixedBiasedPhase_norm_le (1/10000)
      (fun n => (hq _ (fixedBiasedPhase_norm_le n)).le) (D j) hN
    change (1/480 : ℝ) ≤ imaginaryBias (v ∘ L) (D j)
    have hh := (abs_le.mp he).1
    have hb : (1/240 : ℝ) ≤ imaginaryBias fixedBiasedPhase (D j) := fixedBiasedPhase_bias j
    linarith
  by_contra! hn
  have hpair (a b : Fin Q) :
      Tendsto (orderedMean (pairOrder a b ∘ L)) atTop (𝓝 0) :=
    hn (pairOrder a b ∘ q)
  have ht := tendsto_finset_sum (univ : Finset (Fin Q)) (fun a _ =>
    tendsto_finset_sum (univ : Finset (Fin Q)) (fun b _ =>
      ((hpair a b).sub (hpair b a)).const_mul (C a b)))
  simp only [sub_zero,mul_zero,sum_const_zero] at ht
  have hbad : (4 : ℝ)*(1/480) ≤ 0 := by
    apply ge_of_tendsto (ht.comp fixedBiasedPhase_endpoint_tendsto)
    apply Eventually.of_forall
    intro j
    simp only [Function.comp_apply]
    rw [← skew_mean_expansion_pairOrders L C (phaseSkew_swap v)]
    linarith [hbias j]
  norm_num at hbad

/-- Absolute harmonic summability of ALL fixed-multiplier defects still
does not bridge the harmonic/natural gap, even for ONE fixed three-label
sequence with its ordinary order-skew observable. -/
theorem exists_fixed_three_label_summable_defects_natural_gap :
    ∃ L : ℕ → Fin 3,
      (∀ k, 0 < k → Summable
        (fun n => ‖labelDilationDefect k L n / (n : ℝ)‖)) ∧
      (∀ k, 0 < k → Tendsto
        (fun N => prefixMean N (labelDilationDefect k L)) atTop (𝓝 0)) ∧
      Tendsto (fun N => harmonicMean (N+1)
        (fun n => orderSkew (L n) (L (n+1)))) atTop (𝓝 0) ∧
      ¬Tendsto (orderedMean L) atTop (𝓝 0) := by
  obtain ⟨g,hg⟩ := exists_fixed_three_label_map_nonzero
  let L := g ∘ fixedBiasedPhase
  have hL (k : ℕ) (hk : 0 < k) :
      Tendsto (fun N => prefixMean N (labelDilationDefect k L)) atTop (𝓝 0) :=
    mean_dilation_defect_comp_zero fixedBiasedPhase g k
      (fixedBiasedPhase_mean_dilation_defect_zero k hk)
  exact ⟨L,fun k hk => fixedBiasedPhase_comp_summable_harmonic_defects g k hk,
    hL,DilationSpectrum.stable_finite_labels_harmonic_skew_zero L hL
      orderSkew orderSkew_swap orderSkew_abs_le,hg⟩

#print axioms fixedBiasedPhase_comp_summable_harmonic_defects
#print axioms maxPrimeFac_comp_summable_harmonic_defects
#print axioms exists_fixed_three_label_summable_defects_natural_gap
end Erdos371.ExactMultiplierChirpObstruction
