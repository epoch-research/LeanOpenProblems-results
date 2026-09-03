import Submission.BohrIncrementParameters

/-! A relative-rank budget and stable realizations of the supported increment. -/
namespace Erdos3StableSupportedIncrement
open Finset Erdos3BohrIncrementParameters Erdos3SupportedBohrIncrement
  Erdos3FiniteBohr Erdos3BohrCovering Erdos3BohrStableScale Erdos3BohrTranslation
  Erdos3CorrelationSifting Erdos3AsymmetricSifting Erdos3AsymmetricIncrement
  Erdos3BohrLocalAverages Erdos3LocalCorrelationCentering Erdos3CrootSisaskL2
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 3000000

/-- This is a polynomial in the logarithmic support parameter m. -/
def rankBudget (m : ℕ) : ℕ := 32*(1+m*sampleCount m)

lemma log_four_le_two : Real.log (4 : ℝ) ≤ 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have he : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  linarith

lemma rankBudget_bound (m : ℕ) {K : ℝ} (hK : 0 < K) (hKm : K ≤ (2 : ℝ)^(2*m)) :
    16*Real.log (4*K^(sampleCount m)) < (rankBudget m : ℝ)+1 := by
  have hlog : Real.log (4*K^(sampleCount m)) ≤
      2*(1+(m : ℝ)*(sampleCount m : ℝ)) := by
    calc
      _ ≤ Real.log (4*((2 : ℝ)^(2*m))^(sampleCount m)) :=
        Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hK.le hKm _) (by norm_num))
      _ = (1+(m : ℝ)*(sampleCount m : ℝ))*Real.log 4 := by
        rw [show (2 : ℝ)^(2*m) = (4 : ℝ)^m by rw [pow_mul]; norm_num]
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left log_four_le_two
          (by positivity : (0 : ℝ) ≤ 1+(m : ℝ)*(sampleCount m : ℝ))
        nlinarith
  unfold rankBudget
  push_cast
  nlinarith

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma sumset_ratio_pos (T Q : Finset G) (hT : T.Nonempty) (hQ : Q.Nonempty) :
    (0 : ℝ) < (T+Q).card/(T.card : ℝ) := by
  apply div_pos <;> exact_mod_cast (by first | exact (hT.add hQ).card_pos | exact hT.card_pos)

/-- The popular-difference conclusion gives the gain on every smaller averaging window. -/
theorem increment_all_windows (A B S T W : Finset G)
    (E : Finset (AddChar G ℂ)) {q h : ℝ} (hq : 0 ≤ q) (hh : 0 ≤ h)
    (hA : A.Nonempty) (hAB : A ⊆ B) (hS : S.Nonempty) (hT : T.Nonempty)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hfc : ∀ t, (33/32 : ℝ)*f t ≤
      Erdos3CorrelationMoments.corr (localNormalized A B) t/density B)
    (hbad : crossPairDensity S T (fun x ↦ 1-f x) ≤ (1/128 : ℝ)*density S*density T)
    (hW : ∀ s ∈ S, ∀ t ∈ T, t-s ∈ W)
    {m : ℕ} (hm : 0 < m) (hWS : W.card ≤ 2^(2*m)*S.card)
    (hTQ : (T+bohr E q).card ≤ 2^(2*m)*T.card)
    (hgrowth : ((bohr E (q+h)).card : ℝ) ≤
      (1+translationTolerance m (rankBudget m))*((bohr E (q-h)).card : ℝ)) :
    ∃ D : Finset (AddChar G ℂ), D.card ≤ rankBudget m ∧
      ∀ V : Finset G, V.Nonempty →
        V ⊆ bohr (E ∪ D) (min h (generatorRadius m (rankBudget m))) →
        ∃ x : G, (129/128 : ℝ)*relativeDensity A B ≤ smooth V (indicator A) x := by
  have hQ : (bohr E q).Nonempty := ⟨0,bohr_zero E hq⟩
  have hK : ((T+bohr E q).card : ℝ)/T.card ≤ (2 : ℝ)^(2*m) := by
    apply (div_le_iff₀ (by exact_mod_cast hT.card_pos : (0 : ℝ) < T.card)).mpr
    exact_mod_cast hTQ
  have hR := rankBudget_bound m (sumset_ratio_pos T (bohr E q) hT hQ) hK
  obtain ⟨D,hcard,hpop⟩ := exists_supported_relative_popular_periods
    S T (bohr E q) W hS hT hQ f hf hbad hW hm (sampleAccuracy_pos m) hWS
    (walkSteps m) (spectralTolerance_pos (rankBudget m))
    (spectralTolerance_error (rankBudget m)) hR
  refine ⟨D,hcard,?_⟩
  intro V hV hVsub
  have hpop' : ∀ y ∈ V, (63/64 : ℝ) ≤ Erdos3AsymmetricFourierSmoothing.crossSmooth S T f y := by
    intro y hy
    have hy' := hVsub hy
    have hyE : y ∈ bohr E h := by
      apply mem_bohr.mpr
      intro χ hχ
      exact (mem_bohr.mp hy' χ (mem_union_left _ hχ)).trans (min_le_left _ _)
    have hyD : y ∈ bohr D (generatorRadius m (rankBudget m)) := by
      apply mem_bohr.mpr
      intro χ hχ
      exact (mem_bohr.mp hy' χ (mem_union_right _ hχ)).trans (min_le_right _ _)
    have hp := hpop (translationTolerance_pos m (rankBudget m)).le
      (generatorRadius_pos m (rankBudget m)).le y hyD
      (normalized_bohr_translation_le E hq hh
        (translationTolerance_pos m (rankBudget m)).le hgrowth hyE)
    have hl := total_loss m hcard
    linarith
  obtain ⟨x,hx⟩ := local_asymmetric_increment A B S T V hA hAB hS hT hV f
    (by norm_num : (0 : ℝ) ≤ 33/32) hfc hpop'
  refine ⟨x,?_⟩
  exact (mul_le_mul_of_nonneg_right
    (by norm_num : (129/128 : ℝ) ≤ (33/32)*(63/64))
    (relativeDensity_pos A B hA hAB).le).trans hx

/-- The next Bohr set may be regularized at any prescribed fixed tolerance
without sacrificing the relative density gain. -/
theorem stable_increment (A B S T W : Finset G)
    (E : Finset (AddChar G ℂ)) {q h : ℝ} (hq : 0 ≤ q) (hh : 0 < h)
    (hA : A.Nonempty) (hAB : A ⊆ B) (hS : S.Nonempty) (hT : T.Nonempty)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hfc : ∀ t, (33/32 : ℝ)*f t ≤
      Erdos3CorrelationMoments.corr (localNormalized A B) t/density B)
    (hbad : crossPairDensity S T (fun x ↦ 1-f x) ≤ (1/128 : ℝ)*density S*density T)
    (hW : ∀ s ∈ S, ∀ t ∈ T, t-s ∈ W)
    {m : ℕ} (hm : 0 < m) (hWS : W.card ≤ 2^(2*m)*S.card)
    (hTQ : (T+bohr E q).card ≤ 2^(2*m)*T.card)
    (hgrowth : ((bohr E (q+h)).card : ℝ) ≤
      (1+translationTolerance m (rankBudget m))*((bohr E (q-h)).card : ℝ))
    {z : ℕ} (hz : 0 < z) :
    ∃ D : Finset (AddChar G ℂ), D.card ≤ rankBudget m ∧
      let s := min h (generatorRadius m (rankBudget m))
      ∃ r : ℝ, s/2 ≤ r-stabilityWidth (E ∪ D) z (s/2) ∧
        r+stabilityWidth (E ∪ D) z (s/2) ≤ s ∧
        ((bohr (E ∪ D) (r+stabilityWidth (E ∪ D) z (s/2))).card : ℝ) ≤
          (1+1/(z : ℝ))*((bohr (E ∪ D) (r-stabilityWidth (E ∪ D) z (s/2))).card : ℝ) ∧
        ∃ x : G, (129/128 : ℝ)*relativeDensity A B ≤ smooth (bohr (E ∪ D) r) (indicator A) x := by
  obtain ⟨D,hcard,hall⟩ := increment_all_windows A B S T W E hq hh.le hA hAB hS hT
    f hf hfc hbad hW hm hWS hTQ hgrowth
  refine ⟨D,hcard,?_⟩
  let s := min h (generatorRadius m (rankBudget m))
  have hs : 0 < s := lt_min hh (generatorRadius_pos m (rankBudget m))
  obtain ⟨r,hrlo,hrhi,hgrow⟩ := exists_stable_radius (E ∪ D) (by positivity : 0 < s/2) hz
  have hw := stabilityWidth_pos (E ∪ D) hz (by positivity : 0 < s/2)
  refine ⟨r,hrlo,by linarith,hgrow,?_⟩
  exact hall (bohr (E ∪ D) r) ⟨0,bohr_zero _ (by linarith)⟩
    (bohr_mono _ (by linarith : r ≤ s))

#print axioms rankBudget_bound
#print axioms increment_all_windows
#print axioms stable_increment
end Erdos3StableSupportedIncrement
